(** * Queue trace adequacy

    These lemmas relate queue traces to their source operations and cost models.
    For example, insertion records at most three events per occupied heap slot.
    Builds on: CollectionsAuditQueue and CollectionsHeap. *)

From Stdlib Require Import List PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsHeap CollectionsAuditCost CollectionsAuditPrimitive CollectionsAuditCompare
  CollectionsAuditTrie CollectionsAuditPrimitiveAdequacy CollectionsAuditCompareAdequacy
  CollectionsAuditTrieAdequacy CollectionsAuditQueue.
Import List.ListNotations.

(** * Trace accounting *)

(** The work and budget formulas coincide for every queue trace. *)
Theorem queue_model_equation_holds : queue_model_equation_statement.
Proof.
  unfold queue_model_equation_statement, queue_model_work, queue_model_budget.
  intros K E events.
  assert (Hsum :
    fold_right (fun event n => 64 + queue_event_primitive_model E event + n) 0 events =
    64 * length events +
      fold_right (fun event n => queue_event_primitive_model E event + n) 0 events).
  { induction events as [|event events IH].
    - reflexivity.
    - change (64 + queue_event_primitive_model E event +
        fold_right (fun event n => 64 + queue_event_primitive_model E event + n) 0 events =
        64 * S (length events) + (queue_event_primitive_model E event +
        fold_right (fun event n => queue_event_primitive_model E event + n) 0 events)).
      rewrite IH; lia. }
  rewrite Hsum; lia.
Qed.

(** Insertion preserves the source result and limits the number of recorded events. *)
Theorem queue_insert_counted_holds : queue_insert_counted_statement.
Proof.
  unfold queue_insert_counted_statement.
  intros K E tree heap.
  revert tree.
  induction heap as [|slot heap IH]; intros tree; cbn.
  - repeat split; try reflexivity; apply queue_model_equation_holds.
  - destruct slot as [other|].
    + cbn [queue_link].
      destruct (queue_insert (PQueue.link tree other) heap) as [result events] eqn:Hrun.
      specialize (IH (PQueue.link tree other)).
      rewrite Hrun in IH; cbn in IH.
      destruct IH as [Hresult [Hlength Hwork]].
      cbn; repeat split; try congruence; try lia; apply queue_model_equation_holds.
    + cbn; repeat split; try reflexivity; try lia; apply queue_model_equation_holds.
Qed.

(** Selection preserves the source result and records at most two events per slot. *)
Theorem queue_select_counted_holds : queue_select_counted_statement.
Proof.
  unfold queue_select_counted_statement.
  intros K E heap.
  induction heap as [|slot heap IH].
  - cbn; repeat split; try reflexivity; apply queue_model_equation_holds.
  - cbn [queue_select PQueue.select].
    destruct (queue_select heap) as [selected events] eqn:Hrun.
    cbn in IH.
    destruct IH as [Hresult [Hlength Hwork]].
    rewrite <- Hresult.
    destruct selected as [[tree rest]|]; destruct slot as [other|]; cbn;
      repeat split; try reflexivity; try (rewrite length_app; cbn; lia); try lia;
      first [apply queue_model_equation_holds |
        exact (queue_model_equation_holds K E
          (QSelectSlot :: events ++ [QEntryCompare (PQueue.root other) (PQueue.root tree)]))].
Qed.

(** Melding preserves the source heap and bounds the trace by the input slot count. *)
Theorem queue_meld_counted_holds : queue_meld_counted_statement.
Proof.
  unfold queue_meld_counted_statement.
  intros K E a.
  induction a as [|x xs IH]; intros b carry.
  - destruct carry as [tree|]; cbn [queue_meld PQueue.meld].
    + pose proof (queue_insert_counted_holds K E tree b) as Hins.
      destruct (queue_insert tree b) as [result events] eqn:Hrun.
      cbn in Hins.
      destruct Hins as [Hresult [Hlength Hwork]].
      cbn; repeat split; try congruence; try lia; apply queue_model_equation_holds.
    + cbn; repeat split; try reflexivity; try lia; apply queue_model_equation_holds.
  - destruct b as [|y ys].
    + destruct carry as [tree|]; cbn [queue_meld PQueue.meld].
      * pose proof (queue_insert_counted_holds K E tree (x :: xs)) as Hins.
        destruct (queue_insert tree (x :: xs)) as [result events] eqn:Hrun.
        cbn in Hins.
        destruct Hins as [Hresult [Hlength Hwork]].
        cbn; repeat split; try congruence; try lia; apply queue_model_equation_holds.
      * cbn; repeat split; try reflexivity; try lia; apply queue_model_equation_holds.
    + destruct x as [x|], y as [y|], carry as [c|];
        cbn [queue_meld PQueue.meld queue_link];
        destruct (queue_meld xs ys _) as [result events] eqn:Hrun;
        match type of Hrun with
        | queue_meld _ _ ?next = _ => specialize (IH ys next)
        end; rewrite Hrun in IH; cbn in IH;
        destruct IH as [Hresult [Hlength Hwork]];
        rewrite <- Hresult; cbn; repeat split; try reflexivity; try lia;
        apply queue_model_equation_holds.
Qed.

(** Removing a minimum preserves the source result and the trace cost equation. *)
Theorem queue_remove_min_counted_holds : queue_remove_min_counted_statement.
Proof.
  unfold queue_remove_min_counted_statement.
  intros K E heap.
  pose proof (queue_select_counted_holds K E heap) as Hselect.
  unfold queue_remove_min, PQueue.remove_min.
  destruct (queue_select heap) as [selected events] eqn:Hrun.
  cbn in Hselect.
  destruct Hselect as [Hresult _].
  rewrite <- Hresult.
  destruct selected as [[tree rest]|].
  - pose proof (queue_meld_counted_holds K E (PQueue.children_heap tree) rest None) as Hmeld.
    destruct (queue_meld (PQueue.children_heap tree) rest None) as [merged more] eqn:Hmerge.
    cbn in Hmeld.
    destruct Hmeld as [Hmerged _].
    unfold PQueue.merge; rewrite <- Hmerged.
    cbn; split; [reflexivity|apply queue_model_equation_holds].
  - cbn; split; [reflexivity|apply queue_model_equation_holds].
Qed.

(** A counted push returns the same queue as the source operation. *)
Theorem queue_push_counted_holds : queue_push_counted_statement.
Proof.
  unfold queue_push_counted_statement, queue_push, PQueue.push.
  intros K E priority key state.
  destruct (PQueue.priority E key state) as [old|].
  - destruct (BinPos.Pos.ltb priority old).
    + pose proof (queue_insert_counted_holds K E
        (PQueue.Tree (priority, encode E key, key) []) (PQueue.pending state)) as Hins.
      destruct (queue_insert _ _) as [heap events] eqn:Hrun.
      cbn in Hins; destruct Hins as [Hresult _].
      cbn; rewrite <- Hresult; split; [reflexivity|].
      exact (queue_model_equation_holds K E
        (QGet key (PQueue.live state) :: QPriorityLt priority old :: QEncode key ::
          events ++ [QSet key priority (PQueue.live state)])).
    + cbn; split; [reflexivity|].
      exact (queue_model_equation_holds K E
        [QGet key (PQueue.live state); QPriorityLt priority old]).
  - pose proof (queue_insert_counted_holds K E
      (PQueue.Tree (priority, encode E key, key) []) (PQueue.pending state)) as Hins.
    destruct (queue_insert _ _) as [heap events] eqn:Hrun.
    cbn in Hins; destruct Hins as [Hresult _].
    cbn; rewrite <- Hresult; split; [reflexivity|].
    exact (queue_model_equation_holds K E
      (QGet key (PQueue.live state) :: QEncode key ::
        events ++ [QSet key priority (PQueue.live state)])).
Qed.

(** The recorded push follows the actual lookup and insertion branches. *)
Lemma queue_push_execution_holds K (E : encoding K) priority key state :
  let '(result, events) := queue_push E priority key state in
  queue_push_execution E priority key state result events.
Proof.
  unfold queue_push.
  destruct (PQueue.priority E key state) as [old|] eqn:Hpriority.
  - destruct (BinPos.Pos.ltb priority old) eqn:Hlower.
    + destruct (queue_insert (PQueue.Tree (priority, encode E key, key) [])
        (PQueue.pending state)) as [heap events] eqn:Hinsert.
      cbn; eapply QueuePushLower; eauto.
    + eapply QueuePushUnchanged; eauto.
  - destruct (queue_insert (PQueue.Tree (priority, encode E key, key) [])
      (PQueue.pending state)) as [heap events] eqn:Hinsert.
    cbn; eapply QueuePushNew; eauto.
Qed.

(** Fuelled pop records each actual removal, map lookup, and stale-entry continuation. *)
Lemma queue_pop_fuel_execution_holds K (E : encoding K) fuel heap live count :
  let '(result, events) := queue_pop_fuel E fuel heap live count in
  queue_pop_fuel_execution E fuel heap live count result events.
Proof.
  revert heap live count.
  induction fuel as [|fuel IH]; intros heap live count; cbn [queue_pop_fuel].
  - constructor.
  - destruct (queue_remove_min heap) as [selected events] eqn:Hremove.
    destruct selected as [[[[priority code] key] next]|].
    + destruct (Map.get E key live) as [current|] eqn:Hget.
      * destruct (BinPos.Pos.eqb priority current) eqn:Hequal.
        -- apply BinPos.Pos.eqb_eq in Hequal; subst current.
           eapply QueuePopAccepted; eauto.
        -- specialize (IH next live count).
           destruct (queue_pop_fuel E fuel next live count) as [result later] eqn:Hrun.
           eapply QueuePopStale; eauto.
      * specialize (IH next live count).
        destruct (queue_pop_fuel E fuel next live count) as [result later] eqn:Hrun.
        eapply QueuePopMissing; eauto.
    + eapply QueuePopEmpty; eauto.
Qed.

(** Every recorded pop execution returns the source pop result. *)
Lemma queue_pop_execution_result K (E : encoding K) fuel heap live count result events :
  queue_pop_fuel_execution E fuel heap live count result events ->
  result = PQueue.pop_fuel E fuel heap live count.
Proof.
  intro Hexec.
  induction Hexec as
    [heap live count
    |rest heap live count remove_events Hremove
    |rest heap live count priority code key next remove_events Hremove Hget
    |rest heap live count priority code key next current remove_events result later
      Hremove Hget Hequal Hlater IH
    |rest heap live count priority code key next remove_events result later Hremove Hget Hlater IH].
  - reflexivity.
  - pose proof (queue_remove_min_counted_holds K E heap) as Hsource.
    rewrite Hremove in Hsource; cbn in Hsource.
    cbn [PQueue.pop_fuel]; rewrite <- (proj1 Hsource); reflexivity.
  - pose proof (queue_remove_min_counted_holds K E heap) as Hsource.
    rewrite Hremove in Hsource; cbn in Hsource.
    cbn [PQueue.pop_fuel]; rewrite <- (proj1 Hsource), Hget, BinPos.Pos.eqb_refl; reflexivity.
  - pose proof (queue_remove_min_counted_holds K E heap) as Hsource.
    rewrite Hremove in Hsource; cbn in Hsource.
    cbn [PQueue.pop_fuel]; rewrite <- (proj1 Hsource), Hget, Hequal; exact IH.
  - pose proof (queue_remove_min_counted_holds K E heap) as Hsource.
    rewrite Hremove in Hsource; cbn in Hsource.
    cbn [PQueue.pop_fuel]; rewrite <- (proj1 Hsource), Hget; exact IH.
Qed.

(** Both outer traces follow their source branches and return their source results. *)
Theorem queue_outer_execution_holds : queue_outer_execution_statement.
Proof.
  unfold queue_outer_execution_statement.
  split.
  - intros K E priority key state.
    pose proof (queue_push_execution_holds K E priority key state) as Hexec.
    pose proof (queue_push_counted_holds K E priority key state) as Hresult.
    destruct (queue_push E priority key state) as [result events]; cbn in *; tauto.
  - intros K E fuel heap live count.
    pose proof (queue_pop_fuel_execution_holds K E fuel heap live count) as Hexec.
    destruct (queue_pop_fuel E fuel heap live count) as [result events]; cbn in *.
    split; [exact Hexec|eapply queue_pop_execution_result; exact Hexec].
Qed.

(** Fuel-step counts distribute over concatenated trace fragments. *)
Lemma queue_fuel_steps_app K (a b : list (queue_event K)) :
  queue_fuel_steps (a ++ b) = queue_fuel_steps a + queue_fuel_steps b.
Proof.
  unfold queue_fuel_steps; rewrite filter_app, length_app; reflexivity.
Qed.

(** Heap insertion does not record queue fuel steps. *)
Lemma queue_insert_no_fuel K (tree : PQueue.tree K) heap :
  queue_fuel_steps (snd (queue_insert tree heap)) = 0.
Proof.
  revert tree; induction heap as [|slot heap IH]; intros tree; cbn [queue_insert].
  - reflexivity.
  - destruct slot as [other|]; [|reflexivity].
    cbn [queue_link].
    specialize (IH (PQueue.link tree other)).
    destruct (queue_insert (PQueue.link tree other) heap) as [result events].
    cbn in IH; exact IH.
Qed.

(** Heap selection does not record queue fuel steps. *)
Lemma queue_select_no_fuel K (heap : PQueue.heap K) :
  queue_fuel_steps (snd (queue_select heap)) = 0.
Proof.
  induction heap as [|slot heap IH]; cbn [queue_select].
  - reflexivity.
  - destruct (queue_select heap) as [selected events].
    cbn in IH.
    destruct selected as [[tree rest]|]; destruct slot as [other|]; cbn;
      unfold queue_fuel_steps in *; rewrite ?filter_app, ?length_app; cbn in *; lia.
Qed.

(** Heap melding does not record queue fuel steps. *)
Lemma queue_meld_no_fuel K (a b : PQueue.heap K) carry :
  queue_fuel_steps (snd (queue_meld a b carry)) = 0.
Proof.
  revert b carry; induction a as [|x xs IH]; intros b carry.
  - destruct carry as [tree|]; cbn [queue_meld]; [|reflexivity].
    pose proof (queue_insert_no_fuel K tree b) as Hins.
    destruct (queue_insert tree b) as [result events]; cbn in *; exact Hins.
  - destruct b as [|y ys].
    + destruct carry as [tree|]; cbn [queue_meld]; [|reflexivity].
      pose proof (queue_insert_no_fuel K tree (x :: xs)) as Hins.
      destruct (queue_insert tree (x :: xs)) as [result events]; cbn in *; exact Hins.
    + destruct x as [x|], y as [y|], carry as [c|];
        cbn [queue_meld queue_link];
        destruct (queue_meld xs ys _) as [result events] eqn:Hrun;
        match type of Hrun with
        | queue_meld _ _ ?next = _ => specialize (IH ys next)
        end; rewrite Hrun in IH; cbn in IH; exact IH.
Qed.

(** Minimum removal does not itself consume queue fuel. *)
Lemma queue_remove_min_no_fuel K (heap : PQueue.heap K) :
  queue_fuel_steps (snd (queue_remove_min heap)) = 0.
Proof.
  pose proof (queue_select_no_fuel K heap) as Hselect.
  unfold queue_remove_min.
  destruct (queue_select heap) as [selected events];
    change (queue_fuel_steps events = 0) in Hselect.
  destruct selected as [[tree rest]|]; [|exact Hselect].
  pose proof (queue_meld_no_fuel K (PQueue.children_heap tree) rest None) as Hmeld.
  destruct (queue_meld (PQueue.children_heap tree) rest None) as [result more];
    change (queue_fuel_steps more = 0) in Hmeld.
  change (queue_fuel_steps (events ++ [QChildren tree] ++ more) = 0).
  rewrite queue_fuel_steps_app, queue_fuel_steps_app.
  change (queue_fuel_steps events + (0 + queue_fuel_steps more) = 0); lia.
Qed.

(** A fuelled trace prefix adds one step and retains the counts of both fragments. *)
Lemma queue_fuel_steps_prefix K (first last : list (queue_event K)) :
  queue_fuel_steps (QFuelStep :: first ++ last) =
  S (queue_fuel_steps first + queue_fuel_steps last).
Proof.
  change (S (queue_fuel_steps (first ++ last)) =
    S (queue_fuel_steps first + queue_fuel_steps last)).
  rewrite queue_fuel_steps_app; reflexivity.
Qed.

(** An execution takes at most one more fuel step than its supplied fuel. *)
Lemma queue_pop_execution_fuel_bound K (E : encoding K) fuel heap live count result events :
  queue_pop_fuel_execution E fuel heap live count result events ->
  queue_fuel_steps events <= S fuel.
Proof.
  intro Hexec.
  induction Hexec as
    [heap live count
    |rest heap live count remove_events Hremove
    |rest heap live count priority code key next remove_events Hremove Hget
    |rest heap live count priority code key next current remove_events result later
      Hremove Hget Hequal Hlater IH
    |rest heap live count priority code key next remove_events result later Hremove Hget Hlater IH].
  - reflexivity.
  - pose proof (queue_remove_min_no_fuel K heap) as Hzero.
    rewrite Hremove in Hzero; change (queue_fuel_steps remove_events = 0) in Hzero.
    change (S (queue_fuel_steps remove_events) <= S (S rest)); lia.
  - pose proof (queue_remove_min_no_fuel K heap) as Hzero.
    rewrite Hremove in Hzero; change (queue_fuel_steps remove_events = 0) in Hzero.
    rewrite queue_fuel_steps_prefix.
    change (S (queue_fuel_steps remove_events + 0) <= S (S rest)); lia.
  - pose proof (queue_remove_min_no_fuel K heap) as Hzero.
    rewrite Hremove in Hzero; change (queue_fuel_steps remove_events = 0) in Hzero.
    rewrite queue_fuel_steps_prefix.
    change (S (queue_fuel_steps remove_events + queue_fuel_steps later) <= S (S rest)); lia.
  - pose proof (queue_remove_min_no_fuel K heap) as Hzero.
    rewrite Hremove in Hzero; change (queue_fuel_steps remove_events = 0) in Hzero.
    rewrite queue_fuel_steps_prefix.
    change (S (queue_fuel_steps remove_events + queue_fuel_steps later) <= S (S rest)); lia.
Qed.

(** Fuelled pop preserves its source result, bounded steps, and exact trace work. *)
Theorem queue_pop_fuel_counted_holds : queue_pop_fuel_counted_statement.
Proof.
  unfold queue_pop_fuel_counted_statement.
  intros K E fuel heap live count.
  pose proof (queue_pop_fuel_execution_holds K E fuel heap live count) as Hexec.
  destruct (queue_pop_fuel E fuel heap live count) as [result events].
  cbn in Hexec.
  split; [eapply queue_pop_execution_result; exact Hexec|].
  split; [eapply queue_pop_execution_fuel_bound; exact Hexec|].
  apply queue_model_equation_holds.
Qed.

(** Pop preserves its source result, bounded steps, and exact trace work. *)
Theorem queue_pop_counted_holds : queue_pop_counted_statement.
Proof.
  unfold queue_pop_counted_statement, queue_pop, PQueue.pop.
  intros K E state.
  apply queue_pop_fuel_counted_holds.
Qed.

(** * Nested trace agreement *)

(** Nested push erases its captured encoder bodies to the same counted run. *)
Lemma audit_queue_push_nested_erases K B (E : encoding K)
    (encoder : audit_queue_encoder_model K B) priority key state :
  audit_queue_encoder_erases E encoder ->
  let '(result, events) := audit_queue_push_nested encoder priority key state in
  (result, map fst events) = queue_push E priority key state.
Proof.
  intros Herases.
  unfold audit_queue_push_nested, queue_push, audit_queue_encoder_erases in *.
  destruct (encoder key) as [code body] eqn:Hencode.
  specialize (Herases key); rewrite Hencode in Herases; cbn in Herases; subst code.
  unfold PQueue.priority, Map.get, Map.set.
  destruct (Map.code_get (encode E key) (PQueue.live state)) as [old|].
  - destruct (BinPos.Pos.ltb priority old).
    + destruct (queue_insert (PQueue.Tree (priority, encode E key, key) [])
        (PQueue.pending state)) as [heap events].
      cbn; rewrite map_app; cbn; rewrite map_map.
      induction events as [|event events IH]; cbn in *; congruence.
    + reflexivity.
  - destruct (queue_insert (PQueue.Tree (priority, encode E key, key) [])
      (PQueue.pending state)) as [heap events].
    cbn; rewrite map_app; cbn; rewrite map_map.
    induction events as [|event events IH]; cbn in *; congruence.
Qed.

(** Nested fuelled pop erases its captured encoder bodies to the same counted run. *)
Lemma audit_queue_pop_fuel_nested_erases K B (E : encoding K)
    (encoder : audit_queue_encoder_model K B) fuel heap live count :
  audit_queue_encoder_erases E encoder ->
  let '(result, events) := audit_queue_pop_fuel_nested encoder fuel heap live count in
  (result, map fst events) = queue_pop_fuel E fuel heap live count.
Proof.
  intros Herases; revert heap live count.
  induction fuel as [|fuel IH]; intros heap live count; cbn [audit_queue_pop_fuel_nested
    queue_pop_fuel].
  - reflexivity.
  - destruct (queue_remove_min heap) as [selected events].
    destruct selected as [[[[priority code] key] next]|].
    + destruct (encoder key) as [keycode body] eqn:Hencode.
      pose proof (Herases key) as Hcode; rewrite Hencode in Hcode; cbn in Hcode; subst keycode.
      unfold Map.get.
      destruct (Map.code_get (encode E key) live) as [current|].
      * destruct (BinPos.Pos.eqb priority current).
        -- cbn; rewrite map_app, map_map; cbn.
           unfold Map.remove.
           induction events as [|event events IH']; cbn in *; congruence.
        -- specialize (IH next live count).
           destruct (audit_queue_pop_fuel_nested encoder fuel next live count)
             as [result later] eqn:Hrun.
           cbn in IH; rewrite <- IH.
           cbn; rewrite !map_app, map_map; cbn.
           induction events as [|event events IH']; cbn in *; congruence.
      * specialize (IH next live count).
        destruct (audit_queue_pop_fuel_nested encoder fuel next live count)
          as [result later] eqn:Hrun.
        cbn in IH; rewrite <- IH.
        cbn; rewrite !map_app, map_map; cbn.
        induction events as [|event events IH']; cbn in *; congruence.
    + cbn; rewrite map_map.
      induction events as [|event events IH']; cbn in *; congruence.
Qed.

(** Insertion projects to its source operation without requiring a key encoding. *)
Lemma queue_insert_projection K (tree : PQueue.tree K) heap :
  fst (queue_insert tree heap) = PQueue.insert tree heap.
Proof.
  revert tree; induction heap as [|slot heap IH]; intros tree; cbn [queue_insert PQueue.insert].
  - reflexivity.
  - destruct slot as [other|]; [|reflexivity].
    cbn [queue_link]; specialize (IH (PQueue.link tree other)).
    destruct (queue_insert (PQueue.link tree other) heap) as [result events].
    cbn in *; now rewrite IH.
Qed.

(** Selection projects to its source operation without requiring a key encoding. *)
Lemma queue_select_projection K (heap : PQueue.heap K) :
  fst (queue_select heap) = PQueue.select heap.
Proof.
  induction heap as [|slot heap IH]; cbn [queue_select PQueue.select].
  - reflexivity.
  - destruct (queue_select heap) as [selected events]; cbn in IH.
    rewrite <- IH.
    destruct selected as [[tree rest]|]; destruct slot as [other|]; reflexivity.
Qed.

(** Melding projects to its source operation without requiring a key encoding. *)
Lemma queue_meld_projection K (a b : PQueue.heap K) carry :
  fst (queue_meld a b carry) = PQueue.meld a b carry.
Proof.
  revert b carry; induction a as [|x xs IH]; intros b carry.
  - destruct carry as [tree|]; cbn [queue_meld PQueue.meld]; [|reflexivity].
    pose proof (queue_insert_projection K tree b) as Hins.
    destruct (queue_insert tree b); exact Hins.
  - destruct b as [|y ys].
    + destruct carry as [tree|]; cbn [queue_meld PQueue.meld]; [|reflexivity].
      pose proof (queue_insert_projection K tree (x :: xs)) as Hins.
      destruct (queue_insert tree (x :: xs)); exact Hins.
    + destruct x as [x|], y as [y|], carry as [c|];
        cbn [queue_meld PQueue.meld queue_link];
        destruct (queue_meld xs ys _) as [result events] eqn:Hrun;
        match type of Hrun with
        | queue_meld _ _ ?next = _ => specialize (IH ys next)
        end; rewrite Hrun in IH; cbn in IH; now rewrite <- IH.
Qed.

(** Minimum removal projects to its source operation for every heap. *)
Lemma queue_remove_min_projection K (heap : PQueue.heap K) :
  fst (queue_remove_min heap) = PQueue.remove_min heap.
Proof.
  pose proof (queue_select_projection K heap) as Hselect.
  unfold queue_remove_min, PQueue.remove_min.
  destruct (queue_select heap) as [selected events]; cbn in Hselect; rewrite <- Hselect.
  destruct selected as [[tree rest]|]; [|reflexivity].
  pose proof (queue_meld_projection K (PQueue.children_heap tree) rest None) as Hmeld.
  destruct (queue_meld (PQueue.children_heap tree) rest None) as [result more]; cbn in Hmeld.
  unfold PQueue.merge; now rewrite <- Hmeld.
Qed.

(** All traced queue operations project to their source results. *)
Lemma queue_projection_laws_holds : queue_projection_laws.
Proof.
  unfold queue_projection_laws.
  repeat split; intros.
  - apply queue_insert_projection.
  - apply queue_meld_projection.
  - apply queue_select_projection.
  - apply queue_remove_min_projection.
  - pose proof (queue_push_counted_holds K E p k q) as H.
    destruct (queue_push E p k q); exact (proj1 H).
  - pose proof (queue_pop_fuel_counted_holds K E fuel h m n) as H.
    destruct (queue_pop_fuel E fuel h m n); exact (proj1 H).
  - pose proof (queue_pop_counted_holds K E q) as H.
    destruct (queue_pop E q); exact (proj1 H).
Qed.

(** A fuelled input bound supplies the corresponding ordinary-pop bound. *)
Lemma audit_queue_pop_input_from_fuel :
  audit_queue_pop_fuel_input_statement -> audit_queue_pop_input_statement.
Proof.
  unfold audit_queue_pop_fuel_input_statement, audit_queue_pop_input_statement.
  intros Hfuel K E state.
  apply Hfuel.
Qed.

(** Input bounds transfer to the nested push when the encoder returns the same code. *)
Lemma audit_queue_push_nested_from_input :
  audit_queue_push_input_statement -> audit_queue_push_nested_statement.
Proof.
  unfold audit_queue_push_input_statement, audit_queue_push_nested_statement.
  intros Hinput K B E encoder priority key state Herases.
  pose proof (audit_queue_push_nested_erases K B E encoder priority key state Herases) as Herase.
  pose proof (Hinput K E priority key state) as Hbound.
  destruct (audit_queue_push_nested encoder priority key state) as [result events].
  destruct (queue_push E priority key state) as [source trace].
  cbn in Herase; inversion Herase; subst source trace.
  destruct Hbound as [Hresult [Hlength Hwork]].
  rewrite length_map in Hlength.
  repeat split; assumption.
Qed.

(** Input bounds transfer to the nested fuelled pop for the captured encoder run. *)
Lemma audit_queue_pop_fuel_nested_from_input :
  audit_queue_pop_fuel_input_statement -> audit_queue_pop_fuel_nested_statement.
Proof.
  unfold audit_queue_pop_fuel_input_statement, audit_queue_pop_fuel_nested_statement.
  intros Hinput K B E encoder fuel heap live count Herases.
  pose proof (audit_queue_pop_fuel_nested_erases K B E encoder fuel heap live count Herases)
    as Herase.
  pose proof (Hinput K E fuel heap live count) as Hbound.
  destruct (audit_queue_pop_fuel_nested encoder fuel heap live count) as [result events].
  destruct (queue_pop_fuel E fuel heap live count) as [source trace].
  cbn in Herase; inversion Herase; subst source trace.
  destruct Hbound as [Hresult [Hlength Hwork]].
  rewrite length_map in Hlength.
  repeat split; assumption.
Qed.

(** The nested fuelled-pop bound supplies the corresponding ordinary-pop bound. *)
Lemma audit_queue_pop_nested_from_fuel :
  audit_queue_pop_fuel_nested_statement -> audit_queue_pop_nested_statement.
Proof.
  unfold audit_queue_pop_fuel_nested_statement, audit_queue_pop_nested_statement.
  intros Hfuel K B E encoder state Herases.
  apply Hfuel; exact Herases.
Qed.

(** Heap-only events do not contain an encoder call. *)
Definition queue_heap_event {K} (event : queue_event K) : Prop :=
  match event with
  | QGet _ _
  | QSet _ _ _
  | QRemove _ _
  | QEncode _ => False
  | _ => True
  end.

(** Heap insertion emits only heap events. *)
Lemma queue_insert_heap_events K (tree : PQueue.tree K) heap :
  Forall queue_heap_event (snd (queue_insert tree heap)).
Proof.
  revert tree; induction heap as [|slot heap IH]; intros tree; cbn [queue_insert].
  - repeat constructor.
  - destruct slot as [other|]; [|repeat constructor].
    cbn [queue_link].
    specialize (IH (PQueue.link tree other)).
    destruct (queue_insert (PQueue.link tree other) heap) as [result events].
    cbn in IH; repeat constructor; exact IH.
Qed.

(** Heap selection emits only heap events. *)
Lemma queue_select_heap_events K (heap : PQueue.heap K) :
  Forall queue_heap_event (snd (queue_select heap)).
Proof.
  induction heap as [|slot heap IH]; cbn [queue_select].
  - repeat constructor.
  - destruct (queue_select heap) as [selected events]; cbn in IH.
    destruct selected as [[tree rest]|]; destruct slot as [other|]; cbn;
      try (constructor; [exact I|exact IH]);
      constructor; [exact I|apply Forall_app; split; [exact IH|repeat constructor]].
Qed.

(** Heap melding emits only heap events. *)
Lemma queue_meld_heap_events K (a b : PQueue.heap K) carry :
  Forall queue_heap_event (snd (queue_meld a b carry)).
Proof.
  revert b carry; induction a as [|x xs IH]; intros b carry.
  - destruct carry as [tree|]; cbn [queue_meld]; [|repeat constructor].
    pose proof (queue_insert_heap_events K tree b) as Hins.
    destruct (queue_insert tree b); cbn in *; constructor; [exact I|exact Hins].
  - destruct b as [|y ys].
    + destruct carry as [tree|]; cbn [queue_meld]; [|repeat constructor].
      pose proof (queue_insert_heap_events K tree (x :: xs)) as Hins.
      destruct (queue_insert tree (x :: xs)); cbn in *; constructor; [exact I|exact Hins].
    + destruct x as [x|], y as [y|], carry as [c|];
        cbn [queue_meld queue_link];
        destruct (queue_meld xs ys _) as [result events] eqn:Hrun;
        match type of Hrun with
        | queue_meld _ _ ?next = _ => specialize (IH ys next)
        end; rewrite Hrun in IH; cbn in IH;
        repeat constructor; exact IH.
Qed.

(** Minimum removal emits only heap events. *)
Lemma queue_remove_min_heap_events K (heap : PQueue.heap K) :
  Forall queue_heap_event (snd (queue_remove_min heap)).
Proof.
  pose proof (queue_select_heap_events K heap) as Hselect.
  unfold queue_remove_min.
  destruct (queue_select heap) as [selected events]; cbn in Hselect.
  destruct selected as [[tree rest]|]; [|exact Hselect].
  pose proof (queue_meld_heap_events K (PQueue.children_heap tree) rest None) as Hmeld.
  destruct (queue_meld (PQueue.children_heap tree) rest None) as [result more]; cbn in Hmeld.
  cbn; apply Forall_app; split; [exact Hselect|].
  constructor; [exact I|exact Hmeld].
Qed.

(** Heap events need no encoder receipt in a recorded trace. *)
Lemma queue_heap_events_recorded K B (E : encoding K) events :
  Forall queue_heap_event events ->
  audit_queue_recorded_codes E
    (map (fun event => (event, (None, @nil (positive * list B)))) events).
Proof.
  unfold audit_queue_recorded_codes.
  induction 1 as [|event events Hevent Hall IH]; cbn; constructor; [|exact IH].
  destruct event; cbn in *; tauto.
Qed.

(** A recorded push retains the actual encoder codes and observed map lookup. *)
Lemma audit_queue_recorded_push_codes K B (E : encoding K)
    (encoder : audit_queue_encoder_model K B) priority key state :
  audit_queue_encoder_erases E encoder ->
  audit_queue_recorded_codes E (snd (audit_queue_recorded_push encoder priority key state)).
Proof.
  intros Herases.
  unfold audit_queue_recorded_push, audit_queue_push_nested, audit_queue_capture_encoder.
  destruct (encoder key) as [code body] eqn:Hencode.
  pose proof (Herases key) as Hcode; rewrite Hencode in Hcode; cbn in Hcode; subst code.
  fold (Map.get E key (PQueue.live state)).
  destruct (Map.get E key (PQueue.live state)) as [old|] eqn:Hget.
  - destruct (Pos.ltb priority old).
    + pose proof (queue_insert_heap_events K
        (PQueue.Tree (priority, encode E key, key) []) (PQueue.pending state)) as Hins.
      destruct (queue_insert _ _) as [heap events]; cbn in Hins.
      unfold audit_queue_recorded_codes; cbn; constructor.
      * split; [rewrite Hget; reflexivity|eexists; reflexivity].
      * constructor; [split; reflexivity|].
        constructor; [split; [reflexivity|eexists; reflexivity]|].
        apply Forall_app; split.
        -- apply queue_heap_events_recorded; exact Hins.
        -- constructor; [split; [reflexivity|eexists; reflexivity]|constructor].
    + unfold audit_queue_recorded_codes; cbn; constructor.
      * split; [rewrite Hget; reflexivity|eexists; reflexivity].
      * repeat constructor.
  - pose proof (queue_insert_heap_events K
      (PQueue.Tree (priority, encode E key, key) []) (PQueue.pending state)) as Hins.
    destruct (queue_insert _ _) as [heap events]; cbn in Hins.
    unfold audit_queue_recorded_codes; cbn; constructor.
    + split; [rewrite Hget; reflexivity|eexists; reflexivity].
    + constructor; [split; [reflexivity|eexists; reflexivity]|].
      apply Forall_app; split.
      * apply queue_heap_events_recorded; exact Hins.
      * constructor; [split; [reflexivity|eexists; reflexivity]|constructor].
Qed.

(** A fuel step and heap-only events retain any valid recorded suffix. *)
Lemma queue_recorded_heap_prefix K B (E : encoding K) events suffix :
  Forall queue_heap_event events ->
  audit_queue_recorded_codes E suffix ->
  audit_queue_recorded_codes E
    ((QFuelStep, (None, [])) ::
      map (fun event => (event, (None, @nil (positive * list B)))) events ++ suffix).
Proof.
  intros Hheap Hsuffix; unfold audit_queue_recorded_codes at 1.
  constructor; [split; reflexivity|].
  apply Forall_app; split; [apply queue_heap_events_recorded; exact Hheap|exact Hsuffix].
Qed.

(** Accepted-pop suffixes retain the observed lookup and removal receipt. *)
Lemma queue_recorded_accept_suffix K B (E : encoding K) key live priority current
    (body : list B) :
  Map.get E key live = Some current ->
  audit_queue_recorded_codes E
    [(QExamined, (None, []));
     (QGet key live, (Some (Some current), [(encode E key, body)]));
     (QPriorityEq priority current, (None, []));
     (QAccepted, (None, []));
     (QRemove key live, (None, [(encode E key, body)]))].
Proof.
  intro Hget; unfold audit_queue_recorded_codes; cbn.
  constructor; [split; reflexivity|].
  constructor; [split; [rewrite Hget; reflexivity|eexists; reflexivity]|].
  constructor; [split; reflexivity|].
  constructor; [split; reflexivity|].
  constructor; [split; [reflexivity|eexists; reflexivity]|constructor].
Qed.

(** A recorded fuelled pop retains each actual encoder code and observed map lookup. *)
Lemma audit_queue_recorded_pop_fuel_codes K B (E : encoding K)
    (encoder : audit_queue_encoder_model K B) fuel heap live count :
  audit_queue_encoder_erases E encoder ->
  audit_queue_recorded_codes E (snd (audit_queue_recorded_pop_fuel encoder fuel heap live count)).
Proof.
  intros Herases; revert heap live count.
  induction fuel as [|fuel IH]; intros heap live count.
  - unfold audit_queue_recorded_pop_fuel, audit_queue_pop_fuel_nested,
      audit_queue_recorded_codes; repeat constructor.
  - unfold audit_queue_recorded_pop_fuel at 1; cbn [audit_queue_pop_fuel_nested].
    pose proof (queue_remove_min_heap_events K heap) as Hremove.
    destruct (queue_remove_min heap) as [selected events]; cbn in Hremove.
    destruct selected as [[[[priority code] key] next]|].
    + unfold audit_queue_capture_encoder.
      destruct (encoder key) as [keycode body] eqn:Hencode.
      pose proof (Herases key) as Hcode; rewrite Hencode in Hcode; cbn in Hcode; subst keycode.
      fold (Map.get E key live).
      destruct (Map.get E key live) as [current|] eqn:Hget.
      * destruct (Pos.eqb priority current).
        -- cbn [snd]; apply queue_recorded_heap_prefix; [exact Hremove|].
           apply queue_recorded_accept_suffix; exact Hget.
        -- specialize (IH next live count).
           fold (audit_queue_capture_encoder encoder).
           unfold audit_queue_recorded_pop_fuel in IH.
           destruct (audit_queue_pop_fuel_nested (audit_queue_capture_encoder encoder)
             fuel next live count) as [result later]; cbn in IH.
           cbn [snd]; apply queue_recorded_heap_prefix; [exact Hremove|].
           unfold audit_queue_recorded_codes; cbn.
           constructor; [split; reflexivity|].
           constructor; [split; [rewrite Hget; reflexivity|eexists; reflexivity]|].
           repeat (constructor; [split; reflexivity|]); exact IH.
      * specialize (IH next live count).
        fold (audit_queue_capture_encoder encoder).
        unfold audit_queue_recorded_pop_fuel in IH.
        destruct (audit_queue_pop_fuel_nested (audit_queue_capture_encoder encoder)
          fuel next live count) as [result later]; cbn in IH.
        cbn [snd]; apply queue_recorded_heap_prefix; [exact Hremove|].
        unfold audit_queue_recorded_codes; cbn.
        constructor; [split; reflexivity|].
        constructor; [split; [rewrite Hget; reflexivity|eexists; reflexivity]|].
        constructor; [split; reflexivity|exact IH].
    + unfold audit_queue_recorded_codes at 1; cbn.
      constructor; [split; reflexivity|].
      apply queue_heap_events_recorded; exact Hremove.
Qed.

(** Capturing an erasing encoder preserves its returned code. *)
Lemma audit_queue_capture_erases K B (E : encoding K)
    (encoder : audit_queue_encoder_model K B) :
  audit_queue_encoder_erases E encoder ->
  audit_queue_encoder_erases E (audit_queue_capture_encoder encoder).
Proof.
  intros Herases key; specialize (Herases key).
  unfold audit_queue_capture_encoder; destruct (encoder key); exact Herases.
Qed.

(** Recorded bounds follow from the nested bounds and same-run code receipts. *)
Lemma audit_queue_recorded_from_nested :
  audit_queue_push_nested_statement -> audit_queue_pop_nested_statement ->
  audit_queue_recorded_statement.
Proof.
  intros Hpush Hpop; unfold audit_queue_recorded_statement.
  split.
  - intros K B E encoder priority key state Herases.
    pose proof (Hpush K _ E (audit_queue_capture_encoder encoder) priority key state
      (audit_queue_capture_erases K B E encoder Herases)) as Hnested.
    pose proof (audit_queue_recorded_push_codes K B E encoder priority key state Herases) as Hcodes.
    unfold audit_queue_recorded_push in *.
    destruct (audit_queue_push_nested (audit_queue_capture_encoder encoder) priority key state)
      as [result events].
    cbn in Hcodes; destruct Hnested as [Hresult [Htrace [Hlength Hwork]]].
    repeat split; assumption.
  - intros K B E encoder state Herases.
    pose proof (Hpop K _ E (audit_queue_capture_encoder encoder) state
      (audit_queue_capture_erases K B E encoder Herases)) as Hnested.
    pose proof (audit_queue_recorded_pop_fuel_codes K B E encoder
      (PQueue.pending_count state) (PQueue.pending state) (PQueue.live state)
      (PQueue.live_count state) Herases) as Hcodes.
    unfold audit_queue_recorded_pop, audit_queue_pop_nested in *.
    unfold audit_queue_recorded_pop_fuel in Hcodes.
    destruct (audit_queue_pop_fuel_nested (audit_queue_capture_encoder encoder)
      (PQueue.pending_count state) (PQueue.pending state) (PQueue.live state)
      (PQueue.live_count state)) as [result events].
    cbn in Hcodes; destruct Hnested as [Hresult [Htrace [Hlength Hwork]]].
    repeat split; assumption.
Qed.

(** * Input-derived bounds *)

(** A uniform primitive bound lifts to the complete trace model work. *)
Lemma queue_model_work_uniform_bound K (E : encoding K) events bound :
  Forall (fun event => queue_event_primitive_model E event <= bound) events ->
  queue_model_work E events <=
    64 * S (length events) * S (length events) + length events * (64 + bound).
Proof.
  intros Hbound.
  unfold queue_model_work.
  assert (Hfold :
    fold_right (fun event n => 64 + queue_event_primitive_model E event + n) 0 events <=
      length events * (64 + bound)).
  { induction Hbound as [|event events Hevent Htail IH].
    - reflexivity.
    - change (64 + queue_event_primitive_model E event +
        fold_right (fun event n => 64 + queue_event_primitive_model E event + n) 0 events <=
        S (length events) * (64 + bound)).
      nia. }
  lia.
Qed.

(** A uniform recorded-event source bound lifts to the complete internal source work. *)
Lemma queue_recorded_internal_uniform_bound K B
    (events : list (audit_queue_nested_event K (positive * list B))) bound :
  Forall (fun event => audit_queue_recorded_source_event event <= bound) events ->
  audit_queue_recorded_internal_source_work events <= length events * bound.
Proof.
  intro Hbound; unfold audit_queue_recorded_internal_source_work.
  induction Hbound as [|event events Hevent Htail IH].
  - reflexivity.
  - change (audit_queue_recorded_source_event event +
      fold_right (fun event total => audit_queue_recorded_source_event event + total) 0 events <=
      S (length events) * bound).
    nia.
Qed.

(** A push records at most five events plus three per input heap slot. *)
Lemma audit_queue_push_events_linear K (E : encoding K) priority key state :
  length (snd (queue_push E priority key state)) <= 5 + 3 * length (PQueue.pending state).
Proof.
  pose proof (queue_insert_counted_holds K E
    (PQueue.Tree (priority, encode E key, key) []) (PQueue.pending state)) as Hins.
  destruct (queue_insert (PQueue.Tree (priority, encode E key, key) [])
    (PQueue.pending state)) as [heap events] eqn:Hinsert.
  destruct Hins as [_ [Hlength _]].
  unfold queue_push; destruct (PQueue.priority E key state) as [old|];
    try destruct (Pos.ltb priority old); rewrite ?Hinsert; cbn;
    rewrite ?length_app; cbn; lia.
Qed.

(** The published input event envelope covers the actual push trace. *)
Lemma audit_queue_push_events_input_bound K (E : encoding K) priority key state :
  length (snd (queue_push E priority key state)) <=
    audit_queue_input_event_bound 1 (PQueue.pending state).
Proof.
  pose proof (audit_queue_push_events_linear K E priority key state) as Hlinear.
  unfold audit_queue_input_event_bound, audit_queue_input_scale.
  set (size := 1 + 1 + length (PQueue.pending state) +
    length (PQueue.entries (PQueue.pending state))).
  assert (Hsize : length (PQueue.pending state) <= size) by (unfold size; lia).
  change (length (snd (queue_push E priority key state)) <=
    256 * ((S size) * ((S size) * ((S size) * 1)))).
  nia.
Qed.

(** Event and primitive bounds imply the published input model-work envelope. *)
Lemma audit_queue_model_budget_from_dimensions K (E : encoding K) fuel heap live keys numbers
    events :
  let count := audit_queue_input_event_bound fuel heap in
  let size := audit_queue_input_scale fuel heap in
  let width := audit_queue_input_width E heap live keys numbers in
  length events <= count ->
  Forall (fun event => queue_event_primitive_model E event <= 64 + 12 * width + 8 * size)
    events ->
  queue_model_work E events <= audit_queue_input_budget E fuel heap live keys numbers.
Proof.
  intros count size width Hlength Hprimitive.
  pose proof (queue_model_work_uniform_bound K E events (64 + 12 * width + 8 * size)
    Hprimitive) as Hwork.
  unfold audit_queue_input_budget; fold count size width.
  nia.
Qed.

(** Event and internal-source bounds imply the published full input envelope. *)
Lemma audit_queue_full_budget_from_dimensions K B (E : encoding K) fuel heap live keys numbers
    (weight : B -> nat) (events : list (audit_queue_nested_event K (positive * list B))) :
  let count := audit_queue_input_event_bound fuel heap in
  let size := audit_queue_input_scale fuel heap in
  let width := audit_queue_input_width E heap live keys numbers in
  length events <= count ->
  Forall (fun event => audit_queue_recorded_source_event event <=
    256 + 64 * S width + 8 * size) events ->
  audit_queue_recorded_full_source_work weight events <=
    audit_queue_full_input_budget E fuel heap live keys numbers +
      audit_queue_recorded_body_work weight events.
Proof.
  intros count size width Hlength Hsource.
  pose proof (queue_recorded_internal_uniform_bound K B events
    (256 + 64 * S width + 8 * size) Hsource) as Hwork.
  unfold audit_queue_recorded_full_source_work, audit_queue_full_input_budget.
  fold count size width; nia.
Qed.

(** Both comparison operands of an entry fit the stated bit width. *)
Definition queue_entry_width {K} (width : nat) (entry : PQueue.entry K) : Prop :=
  audit_z_bits (BinInt.Z.pos (fst (fst entry))) <= width /\
  audit_z_bits (BinInt.Z.pos (snd (fst entry))) <= width.

(** The root belongs to the entries of its tree. *)
Lemma queue_root_in_entries K (tree : PQueue.tree K) :
  In (PQueue.root tree) (PQueue.tree_entries tree).
Proof.
  destruct tree; cbn; left; reflexivity.
Qed.

(** Linking two width-bounded trees preserves the bound on every entry. *)
Lemma queue_link_entry_width K width (left right : PQueue.tree K) :
  Forall (queue_entry_width width) (PQueue.tree_entries left) ->
  Forall (queue_entry_width width) (PQueue.tree_entries right) ->
  Forall (queue_entry_width width) (PQueue.tree_entries (PQueue.link left right)).
Proof.
  intros Hleft Hright; apply Forall_forall; intros entry Hin.
  apply PQueue.entries_link in Hin; destruct Hin as [Hin|Hin].
  - apply Forall_forall with (x := entry) in Hleft; assumption.
  - apply Forall_forall with (x := entry) in Hright; assumption.
Qed.

(** A comparison of width-bounded entries has bounded modeled primitive work. *)
Lemma queue_entry_compare_primitive_bound K (E : encoding K) width
    (left right : PQueue.entry K) :
  queue_entry_width width left -> queue_entry_width width right ->
  queue_event_primitive_model E (QEntryCompare left right) <= 3 + 6 * width.
Proof.
  intros [Hlp Hlc] [Hrp Hrc].
  change ((1 + audit_z_bits (BinInt.Z.pos (fst (fst left))) +
      audit_z_bits (BinInt.Z.pos (fst (fst right)))) +
    ((1 + audit_z_bits (BinInt.Z.pos (fst (fst left))) +
      audit_z_bits (BinInt.Z.pos (fst (fst right)))) +
    ((1 + audit_z_bits (BinInt.Z.pos (snd (fst left))) +
      audit_z_bits (BinInt.Z.pos (snd (fst right)))) + 0)) <= 3 + 6 * width).
  lia.
Qed.

(** Insertion comparisons use only entries in the supplied tree and heap. *)
Lemma queue_insert_primitive_bound K (E : encoding K) width (tree : PQueue.tree K) heap :
  Forall (queue_entry_width width) (PQueue.tree_entries tree) ->
  Forall (queue_entry_width width) (PQueue.entries heap) ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width)
    (snd (queue_insert tree heap)).
Proof.
  revert tree; induction heap as [|slot heap IH]; intros tree Htree Hheap.
  - cbn [queue_insert]; repeat constructor; cbn [queue_event_primitive_model]; lia.
  - destruct slot as [other|].
    + change (Forall (queue_entry_width width)
        (PQueue.tree_entries other ++ PQueue.entries heap)) in Hheap.
      apply Forall_app in Hheap; destruct Hheap as [Hother Hrest].
      pose proof (queue_link_entry_width K width tree other Htree Hother) as Hlinked.
      specialize (IH (PQueue.link tree other) Hlinked Hrest).
      cbn [queue_insert queue_link].
      destruct (queue_insert (PQueue.link tree other) heap) as [result events]; cbn in IH.
      constructor; [cbn [queue_event_primitive_model]; lia|].
      constructor; [cbn [queue_event_primitive_model]; lia|].
      constructor; [|exact IH].
      apply queue_entry_compare_primitive_bound.
      * apply Forall_forall with (x := PQueue.root tree) in Htree;
          auto using queue_root_in_entries.
      * apply Forall_forall with (x := PQueue.root other) in Hother;
          auto using queue_root_in_entries.
    + cbn [queue_insert]; repeat constructor; cbn [queue_event_primitive_model]; lia.
Qed.

(** Binary and unary positive sizes denote the same number of bits. *)
Lemma queue_positive_size_agrees (p : positive) : Pos.to_nat (Pos.size p) = Pos.size_nat p.
Proof.
  induction p as [p IH|p IH|]; cbn [Pos.size Pos.size_nat].
  - rewrite Pos2Nat.inj_succ, IH; reflexivity.
  - rewrite Pos2Nat.inj_succ, IH; reflexivity.
  - reflexivity.
Qed.

(** The arithmetic weight of a positive equals its encoded bit width. *)
Lemma queue_positive_z_bits (p : positive) : audit_z_bits (BinInt.Z.pos p) = Pos.size_nat p.
Proof.
  unfold audit_z_bits.
  destruct p as [p|p|]; cbn [BinInt.Z.abs BinInt.Z.log2 BinInt.Z.to_nat Pos.size_nat];
    try reflexivity; now rewrite queue_positive_size_agrees.
Qed.

(** Every number in a list is bounded by its folded maximum. *)
Lemma queue_list_max_bound values value :
  In value values -> value <= fold_right Nat.max 0 values.
Proof.
  induction values as [|head tail IH]; cbn; intros Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + subst; apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.

(** Each original heap entry fits the input number-width envelope. *)
Lemma audit_queue_input_entry_width K (E : encoding K) heap live keys numbers entry :
  In entry (PQueue.entries heap) ->
  queue_entry_width (audit_queue_input_width E heap live keys numbers) entry.
Proof.
  intro Hin.
  unfold queue_entry_width; rewrite !queue_positive_z_bits.
  unfold audit_queue_input_width.
  split.
  - eapply Nat.le_trans; [|apply Nat.le_max_r].
    apply queue_list_max_bound; apply in_map_iff; exists (fst (fst entry)); split.
    + reflexivity.
    + apply in_or_app; right; apply in_or_app; left.
      apply in_flat_map; exists entry; split; [exact Hin|cbn; auto].
  - eapply Nat.le_trans; [|apply Nat.le_max_r].
    apply queue_list_max_bound; apply in_map_iff; exists (snd (fst entry)); split.
    + reflexivity.
    + apply in_or_app; right; apply in_or_app; left.
      apply in_flat_map; exists entry; split; [exact Hin|cbn; auto].
Qed.

(** The extra key and priority fit the push input-width envelope. *)
Lemma audit_queue_push_extra_width K (E : encoding K) heap live key priority :
  let width := audit_queue_input_width E heap live [key] [priority] in
  Pos.size_nat (encode E key) <= width /\ Pos.size_nat priority <= width.
Proof.
  intros width; unfold width, audit_queue_input_width.
  split.
  - eapply Nat.le_trans; [|apply Nat.le_max_l].
    apply queue_list_max_bound; apply in_map_iff; exists key; split; [reflexivity|].
    apply in_or_app; left; cbn; auto.
  - eapply Nat.le_trans; [|apply Nat.le_max_r].
    apply queue_list_max_bound; apply in_map_iff; exists priority; split; [reflexivity|].
    apply in_or_app; left; cbn; auto.
Qed.

(** Even a malformed map enumerates the value returned by a successful position lookup. *)
Lemma queue_map_get_enumerated K (E : encoding K) key (live : Map.t K positive) value :
  Map.get E key live = Some value ->
  exists stored, In (stored, value) (Map.elements live).
Proof.
  unfold Map.get, Map.code_get, Map.elements.
  destruct (Trie.get (encode E key) live) as [[stored actual]|] eqn:Hget; cbn;
    intro Hvalue; [|discriminate].
  inversion Hvalue; subst actual; exists stored.
  apply in_map_iff; exists (encode E key, (stored, value)); split; [reflexivity|].
  apply Trie.elements_complete; exact Hget.
Qed.

(** A successful map lookup returns a priority within the input-width envelope. *)
Lemma audit_queue_input_lookup_width K (E : encoding K) heap live keys numbers key priority :
  Map.get E key live = Some priority ->
  Pos.size_nat priority <= audit_queue_input_width E heap live keys numbers.
Proof.
  intro Hget; destruct (queue_map_get_enumerated K E key live priority Hget) as [stored Hin].
  unfold audit_queue_input_width; eapply Nat.le_trans; [|apply Nat.le_max_r].
  apply queue_list_max_bound; apply in_map_iff; exists priority; split; [reflexivity|].
  apply in_or_app; right; apply in_or_app; right.
  apply in_map_iff; exists (stored, priority); split; [reflexivity|exact Hin].
Qed.

(** Encoder and map events fit a bound derived from the encoded key width. *)
Lemma queue_key_events_primitive_bound K (E : encoding K) width key priority live :
  Pos.size_nat (encode E key) <= width ->
  queue_event_primitive_model E (QGet key live) <= 3 + 6 * width /\
  queue_event_primitive_model E (QSet key priority live) <= 3 + 6 * width /\
  queue_event_primitive_model E (QEncode key) <= 3 + 6 * width.
Proof.
  intro Hwidth.
  unfold queue_event_primitive_model, audit_get_weight, audit_set_weight,
    audit_encoding_weight, audit_key_bits_weight.
  lia.
Qed.

(** A priority comparison fits a bound derived from both positive operands. *)
Lemma queue_priority_lt_primitive_bound K (E : encoding K) width priority old :
  Pos.size_nat priority <= width -> Pos.size_nat old <= width ->
  queue_event_primitive_model E (QPriorityLt priority old) <= 3 + 6 * width.
Proof.
  intros Hpriority Hold.
  change (1 + audit_z_bits (BinInt.Z.pos priority) + audit_z_bits (BinInt.Z.pos old) <=
    3 + 6 * width).
  rewrite !queue_positive_z_bits; lia.
Qed.

(** Every primitive in a push trace fits the original input-width envelope. *)
Lemma audit_queue_push_primitive_bound K (E : encoding K) priority key state :
  let width := audit_queue_input_width E (PQueue.pending state) (PQueue.live state)
    [key] [priority] in
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width)
    (snd (queue_push E priority key state)).
Proof.
  intros width.
  pose proof (audit_queue_push_extra_width K E (PQueue.pending state) (PQueue.live state)
    key priority) as [Hkey Hpriority].
  fold width in Hkey, Hpriority.
  assert (Htree : Forall (queue_entry_width width)
      (PQueue.tree_entries (PQueue.Tree (priority, encode E key, key) []))).
  { constructor; [|constructor].
    unfold queue_entry_width; cbn [fst snd]; rewrite !queue_positive_z_bits; auto. }
  assert (Hheap : Forall (queue_entry_width width) (PQueue.entries (PQueue.pending state))).
  { apply Forall_forall; intros entry Hin; unfold width.
    apply audit_queue_input_entry_width; exact Hin. }
  pose proof (queue_insert_primitive_bound K E width _ _ Htree Hheap) as Hins.
  destruct (queue_insert (PQueue.Tree (priority, encode E key, key) [])
    (PQueue.pending state)) as [heap events] eqn:Hinsert.
  change (Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width)
    events) in Hins.
  pose proof (queue_key_events_primitive_bound K E width key priority (PQueue.live state) Hkey)
    as [Hget [Hset Hencode]].
  unfold queue_push.
  destruct (PQueue.priority E key state) as [old|] eqn:Hlookup.
  - assert (Hold : Pos.size_nat old <= width).
    { unfold PQueue.priority in Hlookup; unfold width.
      eapply audit_queue_input_lookup_width; exact Hlookup. }
    pose proof (queue_priority_lt_primitive_bound K E width priority old Hpriority Hold) as Hlt.
    destruct (Pos.ltb priority old); rewrite ?Hinsert; cbn [snd].
    + constructor; [exact Hget|].
      constructor; [exact Hlt|].
      constructor; [exact Hencode|].
      apply Forall_app; split; [exact Hins|].
      constructor; [exact Hset|constructor].
    + constructor; [exact Hget|].
      constructor; [exact Hlt|constructor].
  - rewrite Hinsert; cbn [snd].
    constructor; [exact Hget|].
    constructor; [exact Hencode|].
    apply Forall_app; split; [exact Hins|].
    constructor; [exact Hset|constructor].
Qed.

(** Push preserves its result and fits both bounds derived from its original input. *)
Theorem audit_queue_push_input_holds : audit_queue_push_input_statement.
Proof.
  unfold audit_queue_push_input_statement.
  intros K E priority key state.
  pose proof (queue_push_counted_holds K E priority key state) as Hresult.
  pose proof (audit_queue_push_events_input_bound K E priority key state) as Hlength.
  pose proof (audit_queue_push_primitive_bound K E priority key state) as Hprimitive.
  destruct (queue_push E priority key state) as [result events].
  change (Forall (fun event => queue_event_primitive_model E event <=
    3 + 6 * audit_queue_input_width E (PQueue.pending state) (PQueue.live state)
      [key] [priority]) events) in Hprimitive.
  destruct Hresult as [Hresult _].
  split; [exact Hresult|].
  split; [exact Hlength|].
  apply (audit_queue_model_budget_from_dimensions K E 1 (PQueue.pending state)
    (PQueue.live state) [key] [priority] events); [exact Hlength|].
  eapply Forall_impl; [|exact Hprimitive]; intros event Hevent.
  change (queue_event_primitive_model E event <= 3 +
    6 * audit_queue_input_width E (PQueue.pending state) (PQueue.live state) [key] [priority])
    in Hevent.
  change (queue_event_primitive_model E event <= 64 +
    12 * audit_queue_input_width E (PQueue.pending state) (PQueue.live state) [key] [priority] +
    8 * audit_queue_input_scale 1 (PQueue.pending state)).
  lia.
Qed.

(** Nested push preserves its actual trace and satisfies the original input bounds. *)
Theorem audit_queue_push_nested_holds : audit_queue_push_nested_statement.
Proof.
  apply audit_queue_push_nested_from_input, audit_queue_push_input_holds.
Qed.

(** Selection comparisons use only entries from the original heap. *)
Lemma queue_select_primitive_bound K (E : encoding K) width (heap : PQueue.heap K) :
  Forall (queue_entry_width width) (PQueue.entries heap) ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width)
    (snd (queue_select heap)).
Proof.
  induction heap as [|slot heap IH]; intro Hheap.
  - cbn [queue_select]; repeat constructor; cbn [queue_event_primitive_model]; lia.
  - destruct slot as [other|].
    + change (Forall (queue_entry_width width)
        (PQueue.tree_entries other ++ PQueue.entries heap)) in Hheap.
      apply Forall_app in Hheap; destruct Hheap as [Hother Hrest].
      specialize (IH Hrest).
      pose proof (queue_select_projection K heap) as Hproject.
      pose proof (PQueue.select_entries heap) as Hentries.
      cbn [queue_select].
      destruct (queue_select heap) as [selected events]; cbn in IH, Hproject.
      rewrite <- Hproject in Hentries.
      destruct selected as [[tree rest]|]; [|constructor; [cbn; lia|exact IH]].
      cbn [snd]; constructor; [cbn [queue_event_primitive_model]; lia|].
      apply Forall_app; split; [exact IH|].
      constructor; [|constructor].
      apply queue_entry_compare_primitive_bound.
      * apply Forall_forall with (x := PQueue.root other) in Hother;
          auto using queue_root_in_entries.
      * destruct Hentries as [Hmembers _].
        apply Forall_forall with (x := PQueue.root tree) in Hrest; [exact Hrest|].
        apply Hmembers; left; apply queue_root_in_entries.
    + change (Forall (queue_entry_width width) (PQueue.entries heap)) in Hheap.
      specialize (IH Hheap).
      cbn [queue_select]; destruct (queue_select heap) as [selected events]; cbn in IH.
      destruct selected as [[tree rest]|]; cbn [snd];
        (constructor; [cbn [queue_event_primitive_model]; lia|exact IH]).
Qed.

(** Selection leaves no more heap slots than its original input. *)
Lemma queue_select_rest_length K (heap : PQueue.heap K) tree rest :
  PQueue.select heap = Some (tree, rest) -> length rest <= length heap.
Proof.
  revert tree rest; induction heap as [|slot heap IH]; intros tree rest Hselect.
  - discriminate.
  - cbn [PQueue.select] in Hselect.
    destruct (PQueue.select heap) as [[selected tail]|] eqn:Htail.
    + specialize (IH selected tail eq_refl).
      destruct slot as [other|].
      * destruct (PQueue.precedesb (PQueue.root other) (PQueue.root selected));
          inversion Hselect; subst tree rest;
          unfold PQueue.digit; destruct heap; destruct tail; cbn in *; lia.
      * inversion Hselect; subst tree rest.
        unfold PQueue.digit; destruct heap; destruct tail; cbn in *; lia.
    + destruct slot as [other|]; inversion Hselect; subst tree rest; cbn; lia.
Qed.

(** Inserting a tree increases the heap slot count by at most one. *)
Lemma queue_insert_slots_bound K (tree : PQueue.tree K) heap :
  length (PQueue.insert tree heap) <= S (length heap).
Proof.
  revert tree; induction heap as [|slot heap IH]; intro tree; cbn [PQueue.insert].
  - cbn; lia.
  - destruct slot as [other|]; cbn; [specialize (IH (PQueue.link tree other))|]; lia.
Qed.

(** A digit adds at most one heap slot. *)
Lemma queue_digit_slots_bound K (slot : option (PQueue.tree K)) heap :
  length (PQueue.digit slot heap) <= S (length heap).
Proof.
  destruct slot, heap; reflexivity || (cbn [PQueue.digit length]; lia).
Qed.

(** Melding increases the combined input slot count by at most one. *)
Lemma queue_meld_slots_bound K (a b : PQueue.heap K) carry :
  length (PQueue.meld a b carry) <= S (length a + length b).
Proof.
  revert b carry; induction a as [|x xs IH]; intros b carry.
  - destruct carry as [tree|]; cbn [PQueue.meld length];
      [apply queue_insert_slots_bound|lia].
  - destruct b as [|y ys].
    + destruct carry as [tree|]; cbn [PQueue.meld length];
        [pose proof (queue_insert_slots_bound K tree (x :: xs))|]; cbn in *; lia.
    + destruct x as [x|], y as [y|], carry as [c|]; cbn [PQueue.meld];
        match goal with
        | |- length (PQueue.digit ?slot (PQueue.meld xs ys ?carry)) <= _ =>
          pose proof (queue_digit_slots_bound K slot (PQueue.meld xs ys carry));
          specialize (IH ys carry)
        end; cbn [length] in *; lia.
Qed.

(** Minimum removal preserves remaining-entry membership and decreases the heap count by one. *)
Lemma queue_remove_min_entries K (heap : PQueue.heap K) entry rest :
  PQueue.remove_min heap = Some (entry, rest) ->
  (forall value, In value (PQueue.entries rest) -> In value (PQueue.entries heap)) /\
  PQueue.heap_count heap = S (PQueue.heap_count rest).
Proof.
  unfold PQueue.remove_min.
  pose proof (PQueue.select_entries heap) as Hentries.
  destruct (PQueue.select heap) as [[tree remaining]|] eqn:Hselect; [|discriminate].
  intro Hremove; inversion Hremove; subst entry rest.
  destruct Hentries as [Hmembers Hcount].
  split.
  - intros value Hin; apply Hmembers.
    unfold PQueue.merge in Hin.
    apply PQueue.entries_meld in Hin; cbn in Hin.
    destruct Hin as [Hchild|[Hremaining|Hfalse]]; [left|right|contradiction].
    + apply PQueue.entries_children; right; exact Hchild.
    + exact Hremaining.
  - unfold PQueue.merge; rewrite PQueue.count_meld; cbn.
    rewrite PQueue.count_children in Hcount; lia.
Qed.

(** Each child contributes at least one entry to its tree. *)
Lemma queue_children_slots_bound K (tree : PQueue.tree K) :
  length (PQueue.children_heap tree) <= length (PQueue.tree_entries tree).
Proof.
  destruct tree as [entry children].
  unfold PQueue.children_heap; rewrite length_map, rev_append_rev, app_nil_r, length_rev.
  cbn [PQueue.tree_entries length].
  assert (Hchildren : length children <= length (flat_map PQueue.tree_entries children)).
  { induction children as [|child children IH]; cbn [flat_map length].
    - lia.
    - rewrite length_app; destruct child; cbn [PQueue.tree_entries length] in *; lia. }
  lia.
Qed.

(** A minimum-removal trace is bounded by the input slots and stored entries. *)
Lemma queue_remove_min_events_bound K (E : encoding K) (heap : PQueue.heap K) :
  length (snd (queue_remove_min heap)) <=
    4 + 6 * length heap + 4 * PQueue.heap_count heap.
Proof.
  pose proof (queue_select_counted_holds K E heap) as Hselect.
  pose proof (PQueue.select_entries heap) as Hentries.
  unfold queue_remove_min.
  destruct (queue_select heap) as [selected events] eqn:Hrun.
  destruct Hselect as [Hsource [Hlength _]].
  rewrite <- Hsource in Hentries.
  destruct selected as [[tree remaining]|].
  - pose proof (queue_select_rest_length K heap tree remaining (eq_sym Hsource)) as Hslots.
    pose proof (queue_children_slots_bound K tree) as Hchildren.
    destruct Hentries as [_ Hcount].
    pose proof (queue_meld_counted_holds K E (PQueue.children_heap tree) remaining None) as Hmeld.
    destruct (queue_meld (PQueue.children_heap tree) remaining None) as [result more].
    destruct Hmeld as [_ [Hmore _]].
    cbn [snd]; rewrite !length_app; cbn; lia.
  - cbn [snd]; lia.
Qed.

(** A minimum removal grows the slot count by at most the original entry count plus one. *)
Lemma queue_remove_min_slots_bound K (heap : PQueue.heap K) entry rest :
  PQueue.remove_min heap = Some (entry, rest) ->
  length rest <= 1 + length heap + PQueue.heap_count heap.
Proof.
  unfold PQueue.remove_min.
  pose proof (PQueue.select_entries heap) as Hentries.
  destruct (PQueue.select heap) as [[tree remaining]|] eqn:Hselect; [|discriminate].
  intro Hremove; inversion Hremove; subst entry rest.
  destruct Hentries as [_ Hcount].
  pose proof (queue_select_rest_length K heap tree remaining Hselect) as Hslots.
  pose proof (queue_children_slots_bound K tree) as Hchildren.
  pose proof (queue_meld_slots_bound K (PQueue.children_heap tree) remaining None) as Hmeld.
  unfold PQueue.merge; lia.
Qed.

(** Each pop execution has a quadratic fuel bound in terms of its initial heap. *)
Lemma queue_pop_execution_events_bound K (E : encoding K) fuel heap live count result events :
  queue_pop_fuel_execution E fuel heap live count result events ->
  length events <=
    8 * S fuel * (1 + length heap + S fuel * S (PQueue.heap_count heap)).
Proof.
  intro Hexec.
  induction Hexec as
    [heap live count
    |rest heap live count remove_events Hremove
    |rest heap live count priority code key next remove_events Hremove Hget
    |rest heap live count priority code key next current remove_events result later
      Hremove Hget Hequal Hlater IH
    |rest heap live count priority code key next remove_events result later Hremove Hget Hlater IH].
  - cbn [length]; nia.
  - pose proof (queue_remove_min_events_bound K E heap) as Hbound.
    rewrite Hremove in Hbound; cbn [snd] in Hbound.
    cbn [length]; nia.
  - pose proof (queue_remove_min_events_bound K E heap) as Hbound.
    rewrite Hremove in Hbound; cbn [snd] in Hbound.
    cbn [length]; rewrite length_app; cbn [length]; nia.
  - pose proof (queue_remove_min_events_bound K E heap) as Hbound.
    pose proof (queue_remove_min_projection K heap) as Hsource.
    rewrite Hremove in Hbound, Hsource; cbn [fst snd] in Hbound, Hsource.
    pose proof (queue_remove_min_entries K heap (priority, code, key) next (eq_sym Hsource))
      as [_ Hcount].
    pose proof (queue_remove_min_slots_bound K heap (priority, code, key) next (eq_sym Hsource))
      as Hslots.
    cbn [length]; rewrite !length_app; cbn [length]; nia.
  - pose proof (queue_remove_min_events_bound K E heap) as Hbound.
    pose proof (queue_remove_min_projection K heap) as Hsource.
    rewrite Hremove in Hbound, Hsource; cbn [fst snd] in Hbound, Hsource.
    pose proof (queue_remove_min_entries K heap (priority, code, key) next (eq_sym Hsource))
      as [_ Hcount].
    pose proof (queue_remove_min_slots_bound K heap (priority, code, key) next (eq_sym Hsource))
      as Hslots.
    cbn [length]; rewrite !length_app; cbn [length]; nia.
Qed.

(** The published input event envelope covers every fuelled-pop trace. *)
Lemma audit_queue_pop_fuel_events_input_bound K (E : encoding K) fuel heap live count :
  length (snd (queue_pop_fuel E fuel heap live count)) <=
    audit_queue_input_event_bound fuel heap.
Proof.
  pose proof (queue_pop_fuel_execution_holds K E fuel heap live count) as Hexec.
  destruct (queue_pop_fuel E fuel heap live count) as [result events].
  pose proof (queue_pop_execution_events_bound K E fuel heap live count result events Hexec)
    as Hbound.
  unfold audit_queue_input_event_bound, audit_queue_input_scale.
  unfold PQueue.heap_count in Hbound.
  set (size := 1 + fuel + length heap + length (PQueue.entries heap)).
  assert (Hfuel : S fuel <= S size) by (unfold size; lia).
  assert (Hheap : length heap <= S size) by (unfold size; lia).
  assert (Hentries : S (length (PQueue.entries heap)) <= S size) by (unfold size; lia).
  change (length events <= 256 * (S size * (S size * (S size * 1)))).
  assert (Hproduct : S fuel * S (length (PQueue.entries heap)) <= S size * S size)
    by (apply Nat.mul_le_mono; assumption).
  assert (Hpositive : 1 <= S size) by lia.
  assert (Hsquare : S size <= S size * S size) by nia.
  assert (Hinner : 1 + length heap + S fuel * S (length (PQueue.entries heap)) <=
    3 * (S size * S size)) by nia.
  assert (Hfinal : S fuel * (1 + length heap + S fuel * S (length (PQueue.entries heap))) <=
    S size * (3 * (S size * S size))) by (apply Nat.mul_le_mono; assumption).
  nia.
Qed.

(** A single optional heap slot has the entry-width property exactly when its tree does. *)
Lemma queue_slot_entry_width K width (slot : option (PQueue.tree K)) :
  Forall (queue_entry_width width) (PQueue.slot_entries slot) ->
  match slot with
  | None => True
  | Some tree => Forall (queue_entry_width width) (PQueue.tree_entries tree)
  end.
Proof.
  destruct slot; cbn; auto.
Qed.

(** Width-bounded trees have width-bounded roots. *)
Lemma queue_tree_root_width K width (tree : PQueue.tree K) :
  Forall (queue_entry_width width) (PQueue.tree_entries tree) ->
  queue_entry_width width (PQueue.root tree).
Proof.
  intro Htree; apply Forall_forall with (x := PQueue.root tree) in Htree;
    auto using queue_root_in_entries.
Qed.

(** Melding compares only roots drawn from its two heaps and optional carry. *)
Lemma queue_meld_primitive_bound K (E : encoding K) width (a b : PQueue.heap K) carry :
  Forall (queue_entry_width width) (PQueue.entries a) ->
  Forall (queue_entry_width width) (PQueue.entries b) ->
  (match carry with
   | None => True
   | Some tree => Forall (queue_entry_width width) (PQueue.tree_entries tree)
   end) ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width)
    (snd (queue_meld a b carry)).
Proof.
  revert b carry; induction a as [|x xs IH]; intros b carry Ha Hb Hcarry.
  - destruct carry as [tree|]; cbn [queue_meld].
    + pose proof (queue_insert_primitive_bound K E width tree b Hcarry Hb) as Hins.
      destruct (queue_insert tree b); cbn in Hins; constructor; [cbn; lia|exact Hins].
    + repeat constructor; cbn [queue_event_primitive_model]; lia.
  - destruct b as [|y ys].
    + destruct carry as [tree|]; cbn [queue_meld].
      * pose proof (queue_insert_primitive_bound K E width tree (x :: xs) Hcarry Ha) as Hins.
        destruct (queue_insert tree (x :: xs)); cbn in Hins; constructor; [cbn; lia|exact Hins].
      * repeat constructor; cbn [queue_event_primitive_model]; lia.
    + change (Forall (queue_entry_width width)
        (PQueue.slot_entries x ++ PQueue.entries xs)) in Ha.
      change (Forall (queue_entry_width width)
        (PQueue.slot_entries y ++ PQueue.entries ys)) in Hb.
      apply Forall_app in Ha; destruct Ha as [Hx Hxs].
      apply Forall_app in Hb; destruct Hb as [Hy Hys].
      pose proof (queue_slot_entry_width K width x Hx) as Hx'.
      pose proof (queue_slot_entry_width K width y Hy) as Hy'.
      destruct x as [x|], y as [y|], carry as [c|]; cbn in Hx', Hy', Hcarry;
        cbn [queue_meld queue_link];
        destruct (queue_meld xs ys _) as [result events] eqn:Hrun;
        match type of Hrun with
        | queue_meld _ _ ?next = _ =>
          assert (Hnext :
            match next with
            | None => True
            | Some tree => Forall (queue_entry_width width) (PQueue.tree_entries tree)
            end) by (cbn; auto using queue_link_entry_width);
          specialize (IH ys next Hxs Hys Hnext)
        end;
        rewrite Hrun in IH; cbn in IH;
        repeat (constructor; [cbn [queue_event_primitive_model]; lia|]);
        try (constructor; [apply queue_entry_compare_primitive_bound;
          auto using queue_tree_root_width|exact IH]);
        exact IH.
Qed.

(** Selection preserves entry bounds in the remaining heap and selected children. *)
Lemma queue_select_components_width K width (heap : PQueue.heap K) tree remaining :
  Forall (queue_entry_width width) (PQueue.entries heap) ->
  (forall entry, In entry (PQueue.entries heap) <->
    In entry (PQueue.tree_entries tree) \/ In entry (PQueue.entries remaining)) ->
  Forall (queue_entry_width width) (PQueue.entries (PQueue.children_heap tree)) /\
  Forall (queue_entry_width width) (PQueue.entries remaining).
Proof.
  intros Hheap Hmembers; split.
  - apply Forall_forall; intros entry Hin.
    apply Forall_forall with (x := entry) in Hheap; [exact Hheap|].
    apply Hmembers; left; apply PQueue.entries_children; right; exact Hin.
  - apply Forall_forall; intros entry Hin.
    apply Forall_forall with (x := entry) in Hheap; [exact Hheap|].
    apply Hmembers; right; exact Hin.
Qed.

(** Minimum removal uses bounded entry comparisons and charges its actual child traversal. *)
Lemma queue_remove_min_primitive_bound K (E : encoding K) width (heap : PQueue.heap K) :
  Forall (queue_entry_width width) (PQueue.entries heap) ->
  Forall (fun event => queue_event_primitive_model E event <=
    3 + 6 * width + 2 * PQueue.heap_count heap) (snd (queue_remove_min heap)).
Proof.
  intro Hheap.
  pose proof (queue_select_primitive_bound K E width heap Hheap) as Hselect.
  pose proof (queue_select_projection K heap) as Hsource.
  pose proof (PQueue.select_entries heap) as Hentries.
  unfold queue_remove_min.
  destruct (queue_select heap) as [selected events]; cbn in Hsource, Hselect.
  rewrite <- Hsource in Hentries.
  destruct selected as [[tree remaining]|].
  - destruct Hentries as [Hmembers Hcount].
    destruct (queue_select_components_width K width heap tree remaining Hheap Hmembers)
      as [Hchildren Hremaining].
    pose proof (queue_meld_primitive_bound K E width (PQueue.children_heap tree)
      remaining None Hchildren Hremaining I) as Hmeld.
    destruct (queue_meld (PQueue.children_heap tree) remaining None) as [result more].
    cbn [snd] in Hmeld; cbn [snd].
    rewrite Forall_app; split.
    + eapply Forall_impl; [|exact Hselect]; intros event Hevent.
      change (queue_event_primitive_model E event <= 3 + 6 * width) in Hevent.
      change (queue_event_primitive_model E event <= 3 + 6 * width +
        2 * PQueue.heap_count heap); lia.
    + constructor; [|].
      2: { eapply Forall_impl; [|exact Hmeld]; intros event Hevent.
        change (queue_event_primitive_model E event <= 3 + 6 * width) in Hevent.
        change (queue_event_primitive_model E event <= 3 + 6 * width +
          2 * PQueue.heap_count heap); lia. }
      destruct tree as [entry children].
      pose proof (queue_children_slots_bound K (PQueue.Tree entry children)) as Hslots.
      change (1 + 2 * length children <= 3 + 6 * width + 2 * PQueue.heap_count heap).
      unfold PQueue.children_heap in Hslots.
      rewrite length_map, rev_append_rev, app_nil_r, length_rev in Hslots.
      nia.
  - cbn [snd]; eapply Forall_impl; [|exact Hselect]; intros event Hevent.
    change (queue_event_primitive_model E event <= 3 + 6 * width) in Hevent.
    change (queue_event_primitive_model E event <= 3 + 6 * width +
      2 * PQueue.heap_count heap); lia.
Qed.

(** The entry returned by minimum removal was present in the input heap. *)
Lemma queue_remove_min_entry_in K (heap : PQueue.heap K) entry rest :
  PQueue.remove_min heap = Some (entry, rest) -> In entry (PQueue.entries heap).
Proof.
  unfold PQueue.remove_min.
  pose proof (PQueue.select_entries heap) as Hentries.
  destruct (PQueue.select heap) as [[tree remaining]|] eqn:Hselect; [|discriminate].
  intro Hremove; inversion Hremove; subst entry rest.
  destruct Hentries as [Hmembers _].
  apply Hmembers; left; apply queue_root_in_entries.
Qed.

(** Every original heap entry has an encoded-key width in the input envelope. *)
Lemma audit_queue_input_key_width K (E : encoding K) heap live keys numbers entry :
  In entry (PQueue.entries heap) ->
  Pos.size_nat (encode E (snd entry)) <= audit_queue_input_width E heap live keys numbers.
Proof.
  intro Hin; unfold audit_queue_input_width.
  eapply Nat.le_trans; [|apply Nat.le_max_l].
  apply queue_list_max_bound; apply in_map_iff; exists (snd entry); split; [reflexivity|].
  apply in_or_app; right; apply in_or_app; left.
  apply in_map_iff; exists entry; split; [reflexivity|exact Hin].
Qed.

(** Equality tests and map removals fit bounds derived from their actual operand widths. *)
Lemma queue_pop_event_primitive_bounds K (E : encoding K) width key priority current live :
  Pos.size_nat (encode E key) <= width ->
  Pos.size_nat priority <= width -> Pos.size_nat current <= width ->
  queue_event_primitive_model E (QGet key live) <= 3 + 6 * width /\
  queue_event_primitive_model E (QRemove key live) <= 3 + 6 * width /\
  queue_event_primitive_model E (QPriorityEq priority current) <= 3 + 6 * width.
Proof.
  intros Hkey Hpriority Hcurrent.
  split.
  - change (1 + Pos.size_nat (encode E key) + S (Pos.size_nat (encode E key)) <=
      3 + 6 * width); lia.
  - split.
    + change (1 + 2 * Pos.size_nat (encode E key) + S (Pos.size_nat (encode E key)) <=
        3 + 6 * width); lia.
    + change (1 + audit_z_bits (BinInt.Z.pos priority) + audit_z_bits (BinInt.Z.pos current) <=
        3 + 6 * width).
      rewrite !queue_positive_z_bits; lia.
Qed.

(** A width invariant for original entries is retained by every minimum removal. *)
Lemma queue_remove_min_width_preserved K (E : encoding K) width heap entry rest :
  PQueue.remove_min heap = Some (entry, rest) ->
  Forall (fun value => queue_entry_width width value /\
    Pos.size_nat (encode E (snd value)) <= width) (PQueue.entries heap) ->
  Forall (fun value => queue_entry_width width value /\
    Pos.size_nat (encode E (snd value)) <= width) (PQueue.entries rest).
Proof.
  intros Hremove Hentries.
  destruct (queue_remove_min_entries K heap entry rest Hremove) as [Hsubset _].
  apply Forall_forall; intros value Hin.
  apply Forall_forall with (x := value) in Hentries; [exact Hentries|].
  apply Hsubset; exact Hin.
Qed.

(** A removal retains width invariants and identifies its selected entry in the same heap. *)
Lemma queue_pop_removed_dimensions K (E : encoding K) width cap heap entry next events :
  queue_remove_min heap = (Some (entry, next), events) ->
  Forall (fun value => queue_entry_width width value /\
    Pos.size_nat (encode E (snd value)) <= width) (PQueue.entries heap) ->
  PQueue.heap_count heap <= cap ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap) events /\
  queue_entry_width width entry /\ Pos.size_nat (encode E (snd entry)) <= width /\
  Forall (fun value => queue_entry_width width value /\
    Pos.size_nat (encode E (snd value)) <= width) (PQueue.entries next) /\
  PQueue.heap_count next <= cap.
Proof.
  intros Hremove Hentries Hcap.
  pose proof (queue_remove_min_projection K heap) as Hsource.
  rewrite Hremove in Hsource; cbn [fst] in Hsource.
  assert (Hin : In entry (PQueue.entries heap)).
  { eapply queue_remove_min_entry_in; symmetry; exact Hsource. }
  pose proof Hentries as Hentry.
  apply Forall_forall with (x := entry) in Hentry; [|exact Hin].
  destruct Hentry as [Hwidth Hkey].
  assert (Hheap : Forall (queue_entry_width width) (PQueue.entries heap)).
  { eapply Forall_impl; [|exact Hentries]; intros value [Hvalue _]; exact Hvalue. }
  pose proof (queue_remove_min_primitive_bound K E width heap Hheap) as Hprimitive.
  rewrite Hremove in Hprimitive; cbn [snd] in Hprimitive.
  split.
  - eapply Forall_impl; [|exact Hprimitive]; intros event Hevent.
    change (queue_event_primitive_model E event <=
      3 + 6 * width + 2 * PQueue.heap_count heap) in Hevent.
    change (queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap); lia.
  - split; [exact Hwidth|].
    split; [exact Hkey|].
    split.
    + eapply queue_remove_min_width_preserved; [symmetry; exact Hsource|exact Hentries].
    + destruct (queue_remove_min_entries K heap entry next (eq_sym Hsource)) as [_ Hcount]; lia.
Qed.

(** Lookup and equality events fit the common pop event bound. *)
Lemma queue_pop_lookup_suffix_bound K (E : encoding K) width cap key priority current live :
  Pos.size_nat (encode E key) <= width ->
  Pos.size_nat priority <= width -> Pos.size_nat current <= width ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap)
    [QExamined; QGet key live; QPriorityEq priority current].
Proof.
  intros Hkey Hpriority Hcurrent.
  pose proof (queue_pop_event_primitive_bounds K E width key priority current live
    Hkey Hpriority Hcurrent) as [Hget [_ Heq]].
  constructor; [cbn [queue_event_primitive_model]; lia|].
  constructor; [lia|].
  constructor; [lia|constructor].
Qed.

(** Removing a key fits the common pop event bound. *)
Lemma queue_pop_remove_event_bound K (E : encoding K) width cap key live :
  Pos.size_nat (encode E key) <= width ->
  queue_event_primitive_model E (QRemove key live) <= 3 + 6 * width + 2 * cap.
Proof.
  intro Hkey.
  change (1 + 2 * Pos.size_nat (encode E key) + S (Pos.size_nat (encode E key)) <=
    3 + 6 * width + 2 * cap); lia.
Qed.

(** The accepted-pop suffix is bounded by the actual key and priority widths. *)
Lemma queue_pop_accepted_suffix_bound K (E : encoding K) width cap key priority live :
  Pos.size_nat (encode E key) <= width -> Pos.size_nat priority <= width ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap)
    [QExamined; QGet key live; QPriorityEq priority priority; QAccepted; QRemove key live].
Proof.
  intros Hkey Hpriority.
  pose proof (queue_pop_lookup_suffix_bound K E width cap key priority priority live
    Hkey Hpriority Hpriority) as Hprefix.
  change (Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap)
    ([QExamined; QGet key live; QPriorityEq priority priority] ++ [QAccepted; QRemove key live])).
  apply Forall_app; split; [exact Hprefix|].
  constructor; [cbn [queue_event_primitive_model]; lia|].
  constructor; [apply queue_pop_remove_event_bound; exact Hkey|constructor].
Qed.

(** The stale-pop suffix is bounded by the actual key and compared priorities. *)
Lemma queue_pop_stale_suffix_bound K (E : encoding K) width cap key priority current live :
  Pos.size_nat (encode E key) <= width ->
  Pos.size_nat priority <= width -> Pos.size_nat current <= width ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap)
    [QExamined; QGet key live; QPriorityEq priority current; QStale].
Proof.
  intros Hkey Hpriority Hcurrent.
  pose proof (queue_pop_lookup_suffix_bound K E width cap key priority current live
    Hkey Hpriority Hcurrent) as Hprefix.
  change (Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap)
    ([QExamined; QGet key live; QPriorityEq priority current] ++ [QStale])).
  apply Forall_app; split; [exact Hprefix|].
  constructor; [cbn [queue_event_primitive_model]; lia|constructor].
Qed.

(** An empty removal contributes only its actual bounded heap trace. *)
Lemma queue_pop_empty_events_bound K (E : encoding K) width cap heap events :
  queue_remove_min heap = (None, events) ->
  Forall (fun value => queue_entry_width width value /\
    Pos.size_nat (encode E (snd value)) <= width) (PQueue.entries heap) ->
  PQueue.heap_count heap <= cap ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap) events.
Proof.
  intros Hremove Hentries Hcap.
  assert (Hheap : Forall (queue_entry_width width) (PQueue.entries heap)).
  { eapply Forall_impl; [|exact Hentries]; intros entry [Hwidth _]; exact Hwidth. }
  pose proof (queue_remove_min_primitive_bound K E width heap Hheap) as Hbound.
  rewrite Hremove in Hbound; cbn [snd] in Hbound.
  eapply Forall_impl; [|exact Hbound]; intros event Hevent.
  change (queue_event_primitive_model E event <=
    3 + 6 * width + 2 * PQueue.heap_count heap) in Hevent.
  change (queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap); lia.
Qed.

(** A fuelled execution retains the original entry and lookup width bounds. *)
Lemma queue_pop_execution_primitive_bound K (E : encoding K) fuel heap live count result events :
  queue_pop_fuel_execution E fuel heap live count result events ->
  forall width cap,
  Forall (fun value => queue_entry_width width value /\
    Pos.size_nat (encode E (snd value)) <= width) (PQueue.entries heap) ->
  PQueue.heap_count heap <= cap ->
  (forall key value, Map.get E key live = Some value -> Pos.size_nat value <= width) ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap) events.
Proof.
  intro Hexec.
  induction Hexec as
    [heap live count
    |rest heap live count remove_events Hremove
    |rest heap live count priority code key next remove_events Hremove Hget
    |rest heap live count priority code key next current remove_events result later
      Hremove Hget Hequal Hlater IH
    |rest heap live count priority code key next remove_events result later Hremove Hget Hlater IH];
    intros width cap Hentries Hcap Hlookup.
  - repeat constructor; cbn [queue_event_primitive_model]; lia.
  - constructor; [cbn [queue_event_primitive_model]; lia|].
    eapply queue_pop_empty_events_bound; eauto.
  - destruct (queue_pop_removed_dimensions K E width cap heap (priority, code, key) next
      remove_events Hremove Hentries Hcap) as [Hremove_bound [Hwidth [Hkey [Hnext Hnextcap]]]].
    unfold queue_entry_width in Hwidth; cbn [fst snd] in Hwidth.
    destruct Hwidth as [Hpriority _]; rewrite queue_positive_z_bits in Hpriority.
    constructor; [cbn [queue_event_primitive_model]; lia|].
    apply Forall_app; split; [exact Hremove_bound|].
    apply queue_pop_accepted_suffix_bound; assumption.
  - destruct (queue_pop_removed_dimensions K E width cap heap (priority, code, key) next
      remove_events Hremove Hentries Hcap) as [Hremove_bound [Hwidth [Hkey [Hnext Hnextcap]]]].
    unfold queue_entry_width in Hwidth; cbn [fst snd] in Hwidth.
    destruct Hwidth as [Hpriority _]; rewrite queue_positive_z_bits in Hpriority.
    pose proof (Hlookup key current Hget) as Hcurrent.
    constructor; [cbn [queue_event_primitive_model]; lia|].
    apply Forall_app; split; [exact Hremove_bound|].
    apply Forall_app; split.
    + apply queue_pop_stale_suffix_bound; assumption.
    + apply IH; assumption.
  - destruct (queue_pop_removed_dimensions K E width cap heap (priority, code, key) next
      remove_events Hremove Hentries Hcap) as [Hremove_bound [Hwidth [Hkey [Hnext Hnextcap]]]].
    pose proof (queue_key_events_primitive_bound K E width key priority live Hkey)
      as [Hget_bound _].
    constructor; [cbn [queue_event_primitive_model]; lia|].
    apply Forall_app; split; [exact Hremove_bound|].
    apply Forall_app; split.
    + constructor; [cbn [queue_event_primitive_model]; lia|].
      constructor; [lia|].
      constructor; [cbn [queue_event_primitive_model]; lia|constructor].
    + apply IH; assumption.
Qed.

(** Fuelled pop fits its original input event and model-work envelopes. *)
Theorem audit_queue_pop_fuel_input_holds : audit_queue_pop_fuel_input_statement.
Proof.
  unfold audit_queue_pop_fuel_input_statement.
  intros K E fuel heap live count.
  pose proof (queue_pop_fuel_counted_holds K E fuel heap live count) as Hresult.
  pose proof (audit_queue_pop_fuel_events_input_bound K E fuel heap live count) as Hlength.
  pose proof (queue_pop_fuel_execution_holds K E fuel heap live count) as Hexec.
  destruct (queue_pop_fuel E fuel heap live count) as [result events].
  destruct Hresult as [Hresult _].
  split; [exact Hresult|].
  split; [exact Hlength|].
  apply (audit_queue_model_budget_from_dimensions K E fuel heap live [] [] events);
    [exact Hlength|].
  set (width := audit_queue_input_width E heap live [] []).
  assert (Hentries : Forall (fun entry => queue_entry_width width entry /\
      Pos.size_nat (encode E (snd entry)) <= width) (PQueue.entries heap)).
  { apply Forall_forall; intros entry Hin; split; unfold width.
    - apply audit_queue_input_entry_width; exact Hin.
    - apply audit_queue_input_key_width; exact Hin. }
  assert (Hlookup : forall key value, Map.get E key live = Some value ->
      Pos.size_nat value <= width).
  { intros key value Hget; unfold width; eapply audit_queue_input_lookup_width; exact Hget. }
  pose proof (queue_pop_execution_primitive_bound K E fuel heap live count result events Hexec
    width (PQueue.heap_count heap) Hentries (Nat.le_refl _) Hlookup) as Hprimitive.
  eapply Forall_impl; [|exact Hprimitive]; intros event Hevent.
  change (queue_event_primitive_model E event <=
    3 + 6 * width + 2 * PQueue.heap_count heap) in Hevent.
  change (queue_event_primitive_model E event <= 64 + 12 * width +
    8 * audit_queue_input_scale fuel heap).
  unfold PQueue.heap_count in Hevent.
  unfold audit_queue_input_scale; lia.
Qed.

(** Ordinary pop fits its original input event and model-work envelopes. *)
Theorem audit_queue_pop_input_holds : audit_queue_pop_input_statement.
Proof.
  apply audit_queue_pop_input_from_fuel, audit_queue_pop_fuel_input_holds.
Qed.

(** Nested fuelled pop preserves its trace and original input bounds. *)
Theorem audit_queue_pop_fuel_nested_holds : audit_queue_pop_fuel_nested_statement.
Proof.
  apply audit_queue_pop_fuel_nested_from_input, audit_queue_pop_fuel_input_holds.
Qed.

(** Nested pop preserves its trace and original input bounds. *)
Theorem audit_queue_pop_nested_holds : audit_queue_pop_nested_statement.
Proof.
  apply audit_queue_pop_nested_from_fuel, audit_queue_pop_fuel_nested_holds.
Qed.

(** Recorded push and pop retain their encoder receipts and original input bounds. *)
Theorem audit_queue_recorded_holds : audit_queue_recorded_statement.
Proof.
  apply audit_queue_recorded_from_nested; [apply audit_queue_push_nested_holds|].
  apply audit_queue_pop_nested_holds.
Qed.

(** The queue family combines its execution, projection, counted and recorded contracts. *)
Theorem audit_queue_family_holds : audit_queue_family_statement.
Proof.
  unfold audit_queue_family_statement.
  repeat split; try apply queue_outer_execution_holds; try apply queue_projection_laws_holds;
    try apply queue_insert_counted_holds; try apply queue_select_counted_holds;
    try apply queue_meld_counted_holds; try apply queue_remove_min_counted_holds;
    try apply queue_pop_fuel_counted_holds; try apply audit_queue_push_input_holds;
    try apply audit_queue_pop_fuel_input_holds; try apply audit_queue_pop_input_holds;
    try apply audit_queue_push_nested_holds; try apply audit_queue_pop_fuel_nested_holds;
    try apply audit_queue_pop_nested_holds; apply audit_queue_recorded_holds.
Qed.

(** Heap-only trace events contain no key encoding calls. *)
Lemma queue_heap_events_no_keys K (events : list (queue_event K)) :
  Forall queue_heap_event events ->
  Forall (fun event => queue_event_keys event = []) events.
Proof.
  intro Hheap; induction Hheap as [|event events Hevent Htail IH]; constructor; [|exact IH].
  destruct event; cbn in *; tauto.
Qed.

(** Heap-only events satisfy any bound on the widths of their encoded keys. *)
Lemma queue_heap_events_key_bound K (E : encoding K) width events :
  Forall queue_heap_event events ->
  Forall (fun event => Forall (fun key => Pos.size_nat (encode E key) <= width)
    (queue_event_keys event)) events.
Proof.
  intro Hheap; pose proof (queue_heap_events_no_keys K events Hheap) as Hkeys.
  eapply Forall_impl; [|exact Hkeys]; intros event Hevent; rewrite Hevent; constructor.
Qed.

(** Every encoder key reached by a pop comes from an entry of the initial heap. *)
Lemma queue_pop_execution_key_bound K (E : encoding K) fuel heap live count result events :
  queue_pop_fuel_execution E fuel heap live count result events ->
  forall width cap,
  Forall (fun value => queue_entry_width width value /\
    Pos.size_nat (encode E (snd value)) <= width) (PQueue.entries heap) ->
  PQueue.heap_count heap <= cap ->
  Forall (fun event => Forall (fun key => Pos.size_nat (encode E key) <= width)
    (queue_event_keys event)) events.
Proof.
  intro Hexec.
  induction Hexec as
    [heap live count
    |rest heap live count remove_events Hremove
    |rest heap live count priority code key next remove_events Hremove Hget
    |rest heap live count priority code key next current remove_events result later
      Hremove Hget Hequal Hlater IH
    |rest heap live count priority code key next remove_events result later Hremove Hget Hlater IH];
    intros width cap Hentries Hcap.
  - repeat constructor.
  - pose proof (queue_remove_min_heap_events K heap) as Hheap.
    rewrite Hremove in Hheap; cbn [snd] in Hheap.
    constructor; [constructor|apply queue_heap_events_key_bound; exact Hheap].
  - destruct (queue_pop_removed_dimensions K E width cap heap (priority, code, key) next
      remove_events Hremove Hentries Hcap) as [_ [_ [Hkey [Hnext Hnextcap]]]].
    pose proof (queue_remove_min_heap_events K heap) as Hheap.
    rewrite Hremove in Hheap; cbn [snd] in Hheap.
    constructor; [constructor|].
    apply Forall_app; split; [apply queue_heap_events_key_bound; exact Hheap|].
    repeat constructor; exact Hkey.
  - destruct (queue_pop_removed_dimensions K E width cap heap (priority, code, key) next
      remove_events Hremove Hentries Hcap) as [_ [_ [Hkey [Hnext Hnextcap]]]].
    pose proof (queue_remove_min_heap_events K heap) as Hheap.
    rewrite Hremove in Hheap; cbn [snd] in Hheap.
    constructor; [constructor|].
    apply Forall_app; split; [apply queue_heap_events_key_bound; exact Hheap|].
    apply Forall_app; split.
    + repeat constructor; exact Hkey.
    + apply IH with (cap := cap); assumption.
  - destruct (queue_pop_removed_dimensions K E width cap heap (priority, code, key) next
      remove_events Hremove Hentries Hcap) as [_ [_ [Hkey [Hnext Hnextcap]]]].
    pose proof (queue_remove_min_heap_events K heap) as Hheap.
    rewrite Hremove in Hheap; cbn [snd] in Hheap.
    constructor; [constructor|].
    apply Forall_app; split; [apply queue_heap_events_key_bound; exact Hheap|].
    apply Forall_app; split.
    + repeat constructor; exact Hkey.
    + apply IH with (cap := cap); assumption.
Qed.

(** Every encoder key reached by a push is its supplied key. *)
Lemma queue_push_key_bound K (E : encoding K) priority key state width :
  Pos.size_nat (encode E key) <= width ->
  Forall (fun event => Forall (fun key => Pos.size_nat (encode E key) <= width)
    (queue_event_keys event)) (snd (queue_push E priority key state)).
Proof.
  intro Hkey.
  pose proof (queue_insert_heap_events K (PQueue.Tree (priority, encode E key, key) [])
    (PQueue.pending state)) as Hins.
  destruct (queue_insert (PQueue.Tree (priority, encode E key, key) [])
    (PQueue.pending state)) as [heap events] eqn:Hinsert; cbn [snd] in Hins.
  unfold queue_push; destruct (PQueue.priority E key state) as [old|];
    try destruct (Pos.ltb priority old); rewrite ?Hinsert; cbn [snd].
  - constructor; [repeat constructor; exact Hkey|].
    constructor; [constructor|].
    constructor; [repeat constructor; exact Hkey|].
    apply Forall_app; split; [apply queue_heap_events_key_bound; exact Hins|].
    repeat constructor; exact Hkey.
  - constructor; [repeat constructor; exact Hkey|].
    repeat constructor.
  - constructor; [repeat constructor; exact Hkey|].
    constructor; [repeat constructor; exact Hkey|].
    apply Forall_app; split; [apply queue_heap_events_key_bound; exact Hins|].
    repeat constructor; exact Hkey.
Qed.

(** * Full source-work bounds *)

(** A strict positive comparison costs at most its modeled operand work plus a constant. *)
Lemma queue_ltb_source_model_bound left right :
  audit_queue_ltb_source_work left right <=
  4 + 2 * queue_comparison_model (left, right).
Proof.
  pose proof (audit_positive_order left right) as [_ [_ [Hlt _]]].
  unfold audit_queue_ltb_source_work, queue_comparison_model, audit_binary_weight in *.
  cbn [fst snd] in *; rewrite !queue_positive_z_bits.
  pose proof (Nat.le_min_l (Pos.size_nat left) (Pos.size_nat right)); lia.
Qed.

(** A non-strict positive comparison costs at most its modeled operand work plus a constant. *)
Lemma queue_leb_source_model_bound left right :
  audit_queue_leb_source_work left right <=
  4 + 2 * queue_comparison_model (left, right).
Proof.
  pose proof (audit_positive_order left right) as [_ [_ [_ Hle]]].
  unfold audit_queue_leb_source_work, queue_comparison_model, audit_binary_weight in *.
  cbn [fst snd] in *; rewrite !queue_positive_z_bits.
  pose proof (Nat.le_min_l (Pos.size_nat left) (Pos.size_nat right)); lia.
Qed.

(** A positive equality test costs at most twice the modeled operand work. *)
Lemma queue_eq_source_model_bound left right :
  audit_queue_eq_source_work left right <= 2 * queue_comparison_model (left, right).
Proof.
  pose proof (audit_positive_eqb_source_bound left right) as Heq.
  unfold audit_queue_eq_source_work, queue_comparison_model, audit_binary_weight in *.
  cbn [fst snd] in *; rewrite !queue_positive_z_bits.
  pose proof (Nat.le_min_l (Pos.size_nat left) (Pos.size_nat right)); lia.
Qed.

(** A recorded event's internal source work is priced by its actual model and key width. *)
Lemma queue_recorded_source_event_bound K B (E : encoding K) width
    (recorded : audit_queue_nested_event K (positive * list B)) :
  audit_queue_recorded_codes E [recorded] ->
  Forall (fun key => Pos.size_nat (encode E key) <= width) (queue_event_keys (fst recorded)) ->
  audit_queue_recorded_source_event recorded <=
    100 + 16 * width + 2 * queue_event_primitive_model E (fst recorded).
Proof.
  destruct recorded as [event [observed bodies]].
  unfold audit_queue_recorded_codes; intros Hcodes Hkeys.
  inversion Hcodes as [|? ? Hcode _]; subst.
  destruct event; cbn [queue_event_keys] in Hkeys;
    unfold audit_queue_recorded_source_event; cbn [fst snd] in *;
    try (cbn [queue_event_primitive_model]; lia).
  - pose proof (queue_ltb_source_model_bound (fst (fst a)) (fst (fst b))) as Hlt.
    pose proof (queue_eq_source_model_bound (fst (fst a)) (fst (fst b))) as Heq.
    pose proof (queue_leb_source_model_bound (snd (fst a)) (snd (fst b))) as Hle.
    change (64 + (audit_queue_ltb_source_work (fst (fst a)) (fst (fst b)) +
      audit_queue_eq_source_work (fst (fst a)) (fst (fst b)) +
      audit_queue_leb_source_work (snd (fst a)) (snd (fst b))) <=
      100 + 16 * width + 2 * queue_event_primitive_model E (QEntryCompare a b)).
    unfold queue_event_primitive_model, queue_entry_compare_args; cbn [fold_right]; lia.
  - pose proof (queue_ltb_source_model_bound a b) as Hlt.
    change (64 + audit_queue_ltb_source_work a b <=
      100 + 16 * width + 2 * queue_comparison_model (a, b)); lia.
  - pose proof (queue_eq_source_model_bound a b) as Heq.
    change (64 + audit_queue_eq_source_work a b <=
      100 + 16 * width + 2 * queue_comparison_model (a, b)); lia.
  - destruct Hcode as [_ [body Hbody]]; subst bodies.
    inversion Hkeys as [|? ? Hkey _]; subst.
    pose proof (audit_trie_get_source_work_bound _ (encode E k) m) as Hbound.
    change (64 + (5 + audit_trie_get_source_work (encode E k) m) <=
      100 + 16 * width + 2 * queue_event_primitive_model E (QGet k m)); lia.
  - destruct Hcode as [_ [body Hbody]]; subst bodies.
    inversion Hkeys as [|? ? Hkey _]; subst.
    pose proof (audit_trie_update_source_work_bound _ (encode E k) (Some (k, p)) m) as Hbound.
    change (64 + (2 + audit_trie_update_source_work (encode E k) (Some (k, p)) m) <=
      100 + 16 * width + 2 * queue_event_primitive_model E (QSet k p m)); lia.
  - destruct Hcode as [_ [body Hbody]]; subst bodies.
    inversion Hkeys as [|? ? Hkey _]; subst.
    pose proof (audit_trie_update_source_work_bound _ (encode E k) None m) as Hbound.
    change (64 + (2 + audit_trie_update_source_work (encode E k) None m) <=
      100 + 16 * width + 2 * queue_event_primitive_model E (QRemove k m)); lia.
  - destruct t as [entry children]; cbn [queue_event_primitive_model]; lia.
Qed.

(** Recorded event prices fit the source envelope when keys and primitive work fit their bounds. *)
Lemma queue_recorded_source_dimensions K B (E : encoding K) width cap size
    (events : list (audit_queue_nested_event K (positive * list B))) :
  cap <= size ->
  audit_queue_recorded_codes E events ->
  Forall (fun event => Forall (fun key => Pos.size_nat (encode E key) <= width)
    (queue_event_keys event)) (map fst events) ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap)
    (map fst events) ->
  Forall (fun event => audit_queue_recorded_source_event event <= 256 + 64 * S width + 8 * size)
    events.
Proof.
  intros Hcap Hcodes Hkeys Hprimitive.
  induction events as [|event events IH]; [constructor|].
  unfold audit_queue_recorded_codes in Hcodes; inversion Hcodes as [|? ? Hcode Hcodes']; subst.
  cbn [map] in Hkeys, Hprimitive.
  inversion Hkeys as [|? ? Hkey Hkeys']; subst.
  inversion Hprimitive as [|? ? Hwork Hprimitive']; subst.
  constructor.
  - pose proof (queue_recorded_source_event_bound K B E width event) as Hbound.
    assert (Hsingle : audit_queue_recorded_codes E [event]).
    { unfold audit_queue_recorded_codes; constructor; [exact Hcode|constructor]. }
    specialize (Hbound Hsingle Hkey); nia.
  - apply IH; assumption.
Qed.

(** Recorded push preserves its same-run source execution and input-derived source bound. *)
Theorem audit_queue_recorded_full_push_correct : audit_queue_recorded_full_push_statement.
Proof.
  unfold audit_queue_recorded_full_push_statement.
  intros K B E encoder weight priority key state Herases.
  pose proof (proj1 audit_queue_recorded_holds K B E encoder priority key state Herases) as Hrecord.
  pose proof (proj1 queue_outer_execution_holds K E priority key state) as Houter.
  pose proof (audit_queue_push_primitive_bound K E priority key state) as Hprimitive.
  pose proof (audit_queue_push_extra_width K E (PQueue.pending state) (PQueue.live state)
    key priority) as [Hkey _].
  pose proof (queue_push_key_bound K E priority key state _ Hkey) as Hkeys.
  destruct (audit_queue_recorded_push encoder priority key state) as [result events].
  destruct (queue_push E priority key state) as [source trace].
  destruct Hrecord as [Hresult [Htrace [Hcodes [Hlength Hwork]]]].
  destruct Houter as [Hexec Hsource].
  cbn [snd] in Htrace, Hprimitive, Hkeys; rewrite <- Htrace in Hprimitive, Hkeys.
  split; [exact Hresult|].
  split; [exact Htrace|].
  split.
  - rewrite Htrace.
    assert (Hsame : result = source) by congruence.
    rewrite Hsame; exact Hexec.
  - split; [exact Hcodes|].
    split; [exact Hlength|].
    apply (audit_queue_full_budget_from_dimensions K B E 1 (PQueue.pending state)
      (PQueue.live state) [key] [priority] weight events); [exact Hlength|].
    eapply queue_recorded_source_dimensions with (cap := 0).
    + unfold audit_queue_input_scale; lia.
    + exact Hcodes.
    + exact Hkeys.
    + eapply Forall_impl; [|exact Hprimitive]; intros event Hevent.
      change (queue_event_primitive_model E event <=
        3 + 6 * audit_queue_input_width E (PQueue.pending state) (PQueue.live state)
          [key] [priority]) in Hevent.
      change (queue_event_primitive_model E event <=
        3 + 6 * audit_queue_input_width E (PQueue.pending state) (PQueue.live state)
          [key] [priority] + 2 * 0); lia.
Qed.

(** The input width bounds every heap entry and every successful live-map lookup. *)
Lemma queue_input_width_invariants K (E : encoding K) heap live :
  let width := audit_queue_input_width E heap live [] [] in
  Forall (fun entry => queue_entry_width width entry /\
    Pos.size_nat (encode E (snd entry)) <= width) (PQueue.entries heap) /\
  (forall key value, Map.get E key live = Some value -> Pos.size_nat value <= width).
Proof.
  intros width; split.
  - apply Forall_forall; intros entry Hin; split; unfold width.
    + apply audit_queue_input_entry_width; exact Hin.
    + apply audit_queue_input_key_width; exact Hin.
  - intros key value Hget; unfold width; eapply audit_queue_input_lookup_width; exact Hget.
Qed.

(** Recorded fuelled pop preserves its execution and prices all actual internal source calls. *)
Theorem audit_queue_recorded_full_pop_fuel_correct : audit_queue_recorded_full_pop_fuel_statement.
Proof.
  unfold audit_queue_recorded_full_pop_fuel_statement.
  intros K B E encoder weight fuel heap live count Herases.
  pose proof (audit_queue_pop_fuel_nested_holds K _ E (audit_queue_capture_encoder encoder)
    fuel heap live count (audit_queue_capture_erases K B E encoder Herases)) as Hnested.
  pose proof (audit_queue_recorded_pop_fuel_codes K B E encoder fuel heap live count Herases)
    as Hcodes.
  pose proof (queue_pop_fuel_execution_holds K E fuel heap live count) as Hexec.
  unfold audit_queue_recorded_pop_fuel in *.
  destruct (audit_queue_pop_fuel_nested (audit_queue_capture_encoder encoder) fuel heap live count)
    as [result events].
  destruct (queue_pop_fuel E fuel heap live count) as [source trace].
  destruct Hnested as [Hresult [Htrace [Hlength Hwork]]].
  cbn [snd] in Htrace, Hcodes.
  split; [exact Hresult|].
  split; [exact Htrace|].
  split.
  - rewrite Htrace.
    assert (Hsource : source = PQueue.pop_fuel E fuel heap live count).
    { eapply queue_pop_execution_result; exact Hexec. }
    assert (Hsame : result = source) by congruence; rewrite Hsame; exact Hexec.
  - split; [exact Hcodes|].
    split; [exact Hlength|].
    apply (audit_queue_full_budget_from_dimensions K B E fuel heap live [] [] weight events);
      [exact Hlength|].
    set (width := audit_queue_input_width E heap live [] []).
    pose proof (queue_input_width_invariants K E heap live) as [Hentries Hlookup].
    fold width in Hentries, Hlookup.
    pose proof (queue_pop_execution_primitive_bound K E fuel heap live count source trace Hexec
      width (PQueue.heap_count heap) Hentries (Nat.le_refl _) Hlookup) as Hprimitive.
    pose proof (queue_pop_execution_key_bound K E fuel heap live count source trace Hexec
      width (PQueue.heap_count heap) Hentries (Nat.le_refl _)) as Hkeys.
    rewrite <- Htrace in Hprimitive, Hkeys.
    eapply queue_recorded_source_dimensions with (cap := PQueue.heap_count heap).
    + unfold PQueue.heap_count, audit_queue_input_scale; lia.
    + exact Hcodes.
    + exact Hkeys.
    + exact Hprimitive.
Qed.

(** Recorded pop preserves its execution and prices the same source calls. *)
Theorem audit_queue_recorded_full_pop_correct : audit_queue_recorded_full_pop_statement.
Proof.
  unfold audit_queue_recorded_full_pop_statement, audit_queue_recorded_pop,
    audit_queue_pop_nested, queue_pop, PQueue.pop.
  intros K B E encoder weight state Herases.
  apply audit_queue_recorded_full_pop_fuel_correct; exact Herases.
Qed.

(** The full source contract combines its primitive, queue and recorded obligations. *)
Theorem audit_queue_full_source_contract : audit_queue_full_source_contract_statement.
Proof.
  unfold audit_queue_full_source_contract_statement.
  split; [apply audit_positive_compare_cont|].
  split; [apply audit_positive_order|].
  split; [apply audit_positive_eqb_erases|].
  split; [apply audit_positive_eqb_source_bound|].
  split; [apply audit_trie_get_source_work_bound|].
  split; [apply audit_trie_update_source_work_bound|].
  split; [apply audit_trie_get_trace_adequate|].
  split; [apply audit_trie_update_trace_adequate|].
  split; [apply audit_map_code_get_run_correct|].
  split; [apply audit_queue_family_holds|].
  split; [apply audit_queue_recorded_full_push_correct|].
  split; [apply audit_queue_recorded_full_pop_fuel_correct|].
  apply audit_queue_recorded_full_pop_correct.
Qed.

(** * External encoder receipts *)

(** Captured key events retain exactly the code and body returned by the encoder. *)
Definition queue_recorded_encoder_receipts {K B} (encoder : audit_queue_encoder_model K B)
    (events : list (audit_queue_nested_event K (positive * list B))) : Prop :=
  Forall (fun recorded => let '(event, (_, bodies)) := recorded in
    match event with
    | QGet key _
    | QSet key _ _
    | QRemove key _
    | QEncode key => bodies = [encoder key]
    | _ => bodies = []
    end) events.

(** Heap-only events have no encoder bodies in their recorded form. *)
Lemma queue_heap_recorded_encoder_receipts K B (encoder : audit_queue_encoder_model K B) events :
  Forall queue_heap_event events ->
  queue_recorded_encoder_receipts encoder
    (map (fun event => (event, (None, @nil (positive * list B)))) events).
Proof.
  unfold queue_recorded_encoder_receipts.
  induction 1 as [|event events Hevent Hall IH]; cbn; constructor; [|exact IH].
  destruct event; cbn in *; tauto.
Qed.

(** Recorded push attaches the encoder's actual returned pair to each key event. *)
Lemma queue_recorded_push_encoder_receipts K B (encoder : audit_queue_encoder_model K B)
    priority key state :
  queue_recorded_encoder_receipts encoder
    (snd (audit_queue_recorded_push encoder priority key state)).
Proof.
  unfold audit_queue_recorded_push, audit_queue_push_nested, audit_queue_capture_encoder.
  destruct (encoder key) as [code body] eqn:Hencode.
  destruct (Map.code_get code (PQueue.live state)) as [old|].
  - destruct (Pos.ltb priority old).
    + pose proof (queue_insert_heap_events K (PQueue.Tree (priority, code, key) [])
        (PQueue.pending state)) as Hins.
      destruct (queue_insert _ _) as [heap events]; cbn in Hins.
      unfold queue_recorded_encoder_receipts; cbn; constructor; [now rewrite Hencode|].
      constructor; [reflexivity|].
      constructor; [now rewrite Hencode|].
      apply Forall_app; split; [apply queue_heap_recorded_encoder_receipts; exact Hins|].
      constructor; [now rewrite Hencode|constructor].
    + unfold queue_recorded_encoder_receipts; cbn; constructor; [now rewrite Hencode|].
      repeat constructor.
  - pose proof (queue_insert_heap_events K (PQueue.Tree (priority, code, key) [])
      (PQueue.pending state)) as Hins.
    destruct (queue_insert _ _) as [heap events]; cbn in Hins.
    unfold queue_recorded_encoder_receipts; cbn; constructor; [now rewrite Hencode|].
    constructor; [now rewrite Hencode|].
    apply Forall_app; split; [apply queue_heap_recorded_encoder_receipts; exact Hins|].
    constructor; [now rewrite Hencode|constructor].
Qed.

(** A fuel step and heap events retain a valid encoder-receipt suffix. *)
Lemma queue_encoder_receipts_heap_prefix K B (encoder : audit_queue_encoder_model K B)
    events suffix :
  Forall queue_heap_event events -> queue_recorded_encoder_receipts encoder suffix ->
  queue_recorded_encoder_receipts encoder
    ((QFuelStep, (None, [])) ::
      map (fun event => (event, (None, @nil (positive * list B)))) events ++ suffix).
Proof.
  intros Hheap Hsuffix; unfold queue_recorded_encoder_receipts at 1.
  constructor; [reflexivity|].
  apply Forall_app; split; [apply queue_heap_recorded_encoder_receipts; exact Hheap|exact Hsuffix].
Qed.

(** Recorded fuelled pop attaches the encoder's actual returned pair to each key event. *)
Lemma queue_recorded_pop_fuel_encoder_receipts K B (encoder : audit_queue_encoder_model K B)
    fuel heap live count :
  queue_recorded_encoder_receipts encoder
    (snd (audit_queue_recorded_pop_fuel encoder fuel heap live count)).
Proof.
  revert heap live count; induction fuel as [|fuel IH]; intros heap live count.
  - unfold audit_queue_recorded_pop_fuel, audit_queue_pop_fuel_nested,
      queue_recorded_encoder_receipts; repeat constructor.
  - unfold audit_queue_recorded_pop_fuel at 1; cbn [audit_queue_pop_fuel_nested].
    pose proof (queue_remove_min_heap_events K heap) as Hremove.
    destruct (queue_remove_min heap) as [selected events]; cbn in Hremove.
    destruct selected as [[[[priority code] key] next]|].
    + unfold audit_queue_capture_encoder.
      destruct (encoder key) as [keycode body] eqn:Hencode.
      destruct (Map.code_get keycode live) as [current|].
      * destruct (Pos.eqb priority current).
        -- cbn [snd]; apply queue_encoder_receipts_heap_prefix; [exact Hremove|].
           unfold queue_recorded_encoder_receipts; cbn.
           constructor; [reflexivity|].
           constructor; [now rewrite Hencode|].
           constructor; [reflexivity|].
           constructor; [reflexivity|].
           constructor; [now rewrite Hencode|constructor].
        -- specialize (IH next live count).
           fold (audit_queue_capture_encoder encoder).
           unfold audit_queue_recorded_pop_fuel in IH.
           destruct (audit_queue_pop_fuel_nested (audit_queue_capture_encoder encoder)
             fuel next live count) as [result later]; cbn in IH.
           cbn [snd]; apply queue_encoder_receipts_heap_prefix; [exact Hremove|].
           unfold queue_recorded_encoder_receipts; cbn.
           constructor; [reflexivity|].
           constructor; [now rewrite Hencode|].
           repeat (constructor; [reflexivity|]); exact IH.
      * specialize (IH next live count).
        fold (audit_queue_capture_encoder encoder).
        unfold audit_queue_recorded_pop_fuel in IH.
        destruct (audit_queue_pop_fuel_nested (audit_queue_capture_encoder encoder)
          fuel next live count) as [result later]; cbn in IH.
        cbn [snd]; apply queue_encoder_receipts_heap_prefix; [exact Hremove|].
        unfold queue_recorded_encoder_receipts; cbn.
        constructor; [reflexivity|].
        constructor; [now rewrite Hencode|].
        constructor; [reflexivity|exact IH].
    + unfold queue_recorded_encoder_receipts at 1; cbn.
      constructor; [reflexivity|].
      apply queue_heap_recorded_encoder_receipts; exact Hremove.
Qed.

(** An actual encoder receipt costs at most its external budget plus one receipt unit. *)
Lemma queue_encoder_receipt_budget K B (E : encoding K)
    (encoder : audit_queue_encoder_model K B) (weight : B -> nat) source budget
    (recorded : audit_queue_nested_event K (positive * list B)) :
  audit_queue_external_encoder_adapter E encoder weight source budget ->
  queue_recorded_encoder_receipts encoder [recorded] ->
  audit_queue_recorded_body_work weight [recorded] <=
    1 + audit_queue_recorded_encoder_budget budget [recorded].
Proof.
  intros Hadapter Hreceipt.
  destruct recorded as [event [observed bodies]].
  unfold queue_recorded_encoder_receipts in Hreceipt.
  inversion Hreceipt as [|? ? Hbody _]; subst.
  destruct event; cbn in Hbody; subst bodies;
    unfold audit_queue_recorded_body_work, audit_queue_nested_body_work,
      audit_queue_recorded_encoder_budget; cbn [fst snd fold_right
      audit_queue_recorded_encoder_budget_event];
    try lia;
    try
      match goal with
      | |- context [encoder ?key] =>
        destruct (encoder key) as [code body] eqn:Hencode;
        pose proof (audit_queue_external_encoder_source _ _ _ _ _ Hadapter key code body Hencode)
          as [_ Hbudget]; cbn; lia
      end.
Qed.

(** Actual recorded encoder bodies obey their aggregate external budgets and receipt count. *)
Lemma queue_encoder_receipts_budget K B (E : encoding K)
    (encoder : audit_queue_encoder_model K B) (weight : B -> nat) source budget
    (events : list (audit_queue_nested_event K (positive * list B))) :
  audit_queue_external_encoder_adapter E encoder weight source budget ->
  queue_recorded_encoder_receipts encoder events ->
  audit_queue_recorded_body_work weight events <=
    length events + audit_queue_recorded_encoder_budget budget events.
Proof.
  intros Hadapter Hreceipts.
  induction events as [|event events IH]; [reflexivity|].
  unfold queue_recorded_encoder_receipts in Hreceipts.
  inversion Hreceipts as [|? ? Hreceipt Htail]; subst.
  assert (Hone : queue_recorded_encoder_receipts encoder [event]).
  { unfold queue_recorded_encoder_receipts; constructor; [exact Hreceipt|constructor]. }
  pose proof (queue_encoder_receipt_budget K B E encoder weight source budget event Hadapter Hone)
    as Hbound.
  specialize (IH Htail).
  unfold audit_queue_recorded_body_work, audit_queue_nested_body_work,
    audit_queue_recorded_encoder_budget in *.
  cbn [fold_right length] in *; lia.
Qed.

(** Each source-event bound leaves one unit for a possible encoder receipt. *)
Lemma queue_recorded_source_dimensions_with_receipts K B (E : encoding K) width cap size
    (events : list (audit_queue_nested_event K (positive * list B))) :
  cap <= size ->
  audit_queue_recorded_codes E events ->
  Forall (fun event => Forall (fun key => Pos.size_nat (encode E key) <= width)
    (queue_event_keys event)) (map fst events) ->
  Forall (fun event => queue_event_primitive_model E event <= 3 + 6 * width + 2 * cap)
    (map fst events) ->
  Forall (fun event => 1 + audit_queue_recorded_source_event event <=
    256 + 64 * S width + 8 * size) events.
Proof.
  intros Hcap Hcodes Hkeys Hprimitive.
  induction events as [|event events IH]; [constructor|].
  unfold audit_queue_recorded_codes in Hcodes; inversion Hcodes as [|? ? Hcode Hcodes']; subst.
  cbn [map] in Hkeys, Hprimitive.
  inversion Hkeys as [|? ? Hkey Hkeys']; subst.
  inversion Hprimitive as [|? ? Hwork Hprimitive']; subst.
  constructor.
  - pose proof (queue_recorded_source_event_bound K B E width event) as Hbound.
    assert (Hsingle : audit_queue_recorded_codes E [event]).
    { unfold audit_queue_recorded_codes; constructor; [exact Hcode|constructor]. }
    specialize (Hbound Hsingle Hkey); nia.
  - apply IH; assumption.
Qed.

(** Internal work plus one unit per event fits an aggregate uniform source bound. *)
Lemma queue_internal_work_receipts_bound K B
    (events : list (audit_queue_nested_event K (positive * list B))) bound :
  Forall (fun event => 1 + audit_queue_recorded_source_event event <= bound) events ->
  audit_queue_recorded_internal_source_work events + length events <= length events * bound.
Proof.
  intro Hbound; unfold audit_queue_recorded_internal_source_work.
  induction Hbound as [|event events Hevent Htail IH].
  - reflexivity.
  - change (audit_queue_recorded_source_event event +
      fold_right (fun event total => audit_queue_recorded_source_event event + total) 0 events +
      S (length events) <= S (length events) * bound).
    nia.
Qed.

(** Source dimensions and actual encoder receipts imply the external body-budget bound. *)
Lemma queue_external_source_budget K B (E : encoding K) encoder weight source budget
    fuel heap live keys numbers (events : list (audit_queue_nested_event K (positive * list B))) :
  audit_queue_external_encoder_adapter E encoder weight source budget ->
  queue_recorded_encoder_receipts encoder events ->
  length events <= audit_queue_input_event_bound fuel heap ->
  Forall (fun event => 1 + audit_queue_recorded_source_event event <=
    256 + 64 * S (audit_queue_input_width E heap live keys numbers) +
      8 * audit_queue_input_scale fuel heap) events ->
  audit_queue_recorded_full_source_work weight events <=
    audit_queue_full_input_budget E fuel heap live keys numbers +
      audit_queue_recorded_encoder_budget budget events.
Proof.
  intros Hadapter Hreceipts Hlength Hsource.
  pose proof (queue_encoder_receipts_budget K B E encoder weight source budget events
    Hadapter Hreceipts) as Hbody.
  pose proof (queue_internal_work_receipts_bound K B events _ Hsource) as Hinternal.
  unfold audit_queue_recorded_full_source_work, audit_queue_full_input_budget.
  nia.
Qed.

(** An external encoder's actual push bodies fit its stated per-key budgets. *)
Theorem audit_queue_external_encoder_push_correct : audit_queue_external_encoder_push_statement.
Proof.
  unfold audit_queue_external_encoder_push_statement.
  intros K B E encoder weight source budget priority key state Hadapter.
  pose proof (audit_queue_external_encoder_value _ _ _ _ _ Hadapter) as Herases.
  pose proof (proj1 audit_queue_recorded_holds K B E encoder priority key state Herases) as Hrecord.
  pose proof (queue_recorded_push_encoder_receipts K B encoder priority key state) as Hreceipts.
  pose proof (audit_queue_push_primitive_bound K E priority key state) as Hprimitive.
  pose proof (audit_queue_push_extra_width K E (PQueue.pending state) (PQueue.live state)
    key priority) as [Hkey _].
  pose proof (queue_push_key_bound K E priority key state _ Hkey) as Hkeys.
  unfold audit_queue_recorded_push in Hrecord, Hreceipts.
  destruct (audit_queue_push_nested (audit_queue_capture_encoder encoder) priority key state)
    as [result events].
  destruct (queue_push E priority key state) as [source_result trace].
  destruct Hrecord as [Hresult [Htrace [Hcodes [Hlength Hwork]]]].
  cbn [snd] in Htrace, Hreceipts, Hprimitive, Hkeys.
  rewrite <- Htrace in Hprimitive, Hkeys.
  split; [exact Hresult|].
  apply (queue_external_source_budget K B E encoder weight source budget 1
    (PQueue.pending state) (PQueue.live state) [key] [priority] events);
    try assumption.
  eapply queue_recorded_source_dimensions_with_receipts with (cap := 0).
  - unfold audit_queue_input_scale; lia.
  - exact Hcodes.
  - exact Hkeys.
  - eapply Forall_impl; [|exact Hprimitive]; intros event Hevent.
    change (queue_event_primitive_model E event <=
      3 + 6 * audit_queue_input_width E (PQueue.pending state) (PQueue.live state)
        [key] [priority]) in Hevent.
    change (queue_event_primitive_model E event <=
      3 + 6 * audit_queue_input_width E (PQueue.pending state) (PQueue.live state)
        [key] [priority] + 2 * 0); lia.
Qed.

(** An external encoder's actual fuelled-pop bodies fit its stated per-key budgets. *)
Theorem audit_queue_external_encoder_pop_fuel_correct :
  audit_queue_external_encoder_pop_fuel_statement.
Proof.
  unfold audit_queue_external_encoder_pop_fuel_statement.
  intros K B E encoder weight source budget fuel heap live count Hadapter.
  pose proof (audit_queue_external_encoder_value _ _ _ _ _ Hadapter) as Herases.
  pose proof (audit_queue_pop_fuel_nested_holds K _ E (audit_queue_capture_encoder encoder)
    fuel heap live count (audit_queue_capture_erases K B E encoder Herases)) as Hnested.
  pose proof (audit_queue_recorded_pop_fuel_codes K B E encoder fuel heap live count Herases)
    as Hcodes.
  pose proof (queue_recorded_pop_fuel_encoder_receipts K B encoder fuel heap live count)
    as Hreceipts.
  pose proof (queue_pop_fuel_execution_holds K E fuel heap live count) as Hexec.
  unfold audit_queue_recorded_pop_fuel in *.
  destruct (audit_queue_pop_fuel_nested (audit_queue_capture_encoder encoder) fuel heap live count)
    as [result events].
  destruct (queue_pop_fuel E fuel heap live count) as [source_result trace].
  destruct Hnested as [Hresult [Htrace [Hlength Hwork]]].
  cbn [snd] in Htrace, Hcodes, Hreceipts.
  split; [exact Hresult|].
  apply (queue_external_source_budget K B E encoder weight source budget fuel heap live [] []
    events); try assumption.
  set (width := audit_queue_input_width E heap live [] []).
  assert (Hentries : Forall (fun entry => queue_entry_width width entry /\
      Pos.size_nat (encode E (snd entry)) <= width) (PQueue.entries heap)).
  { apply Forall_forall; intros entry Hin; split; unfold width.
    - apply audit_queue_input_entry_width; exact Hin.
    - apply audit_queue_input_key_width; exact Hin. }
  assert (Hlookup : forall key value, Map.get E key live = Some value ->
      Pos.size_nat value <= width).
  { intros key value Hget; unfold width; eapply audit_queue_input_lookup_width; exact Hget. }
  pose proof (queue_pop_execution_primitive_bound K E fuel heap live count source_result trace Hexec
    width (PQueue.heap_count heap) Hentries (Nat.le_refl _) Hlookup) as Hprimitive.
  pose proof (queue_pop_execution_key_bound K E fuel heap live count source_result trace Hexec
    width (PQueue.heap_count heap) Hentries (Nat.le_refl _)) as Hkeys.
  rewrite <- Htrace in Hprimitive, Hkeys.
  eapply queue_recorded_source_dimensions_with_receipts with (cap := PQueue.heap_count heap).
  - unfold PQueue.heap_count, audit_queue_input_scale; lia.
  - exact Hcodes.
  - exact Hkeys.
  - exact Hprimitive.
Qed.

(** An external encoder's ordinary-pop bodies fit its stated per-key budgets. *)
Theorem audit_queue_external_encoder_pop_correct : audit_queue_external_encoder_pop_statement.
Proof.
  unfold audit_queue_external_encoder_pop_statement, audit_queue_pop_nested, queue_pop, PQueue.pop.
  intros K B E encoder weight source budget state Hadapter.
  exact (audit_queue_external_encoder_pop_fuel_correct K B E encoder weight source budget
    (PQueue.pending_count state) (PQueue.pending state) (PQueue.live state)
    (PQueue.live_count state) Hadapter).
Qed.
