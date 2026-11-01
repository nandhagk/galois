(** * Declared worklist input budget adequacy

    The mathematical budgets bound the work of the same recorded execution.
    For example, a queue key receipt pays for both its entry and the encoder call.
    Builds on: FixpointAuditWorklistAdequacy and collection source bounds. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsHeap CollectionsAuditCost CollectionsAuditTrie CollectionsAuditTrieAdequacy
  CollectionsAuditQueue CollectionsAuditQueueAdequacy.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointAuditWorklist FixpointAuditWorklistBudget FixpointAuditWorklistAdequacy.
Import List.ListNotations.

(** * Queue and trie input bounds *)

Lemma fx_queue_body_bound C (EC : encoding C) events :
  queue_recorded_encoder_receipts (fx_index_encoder EC) events ->
  audit_queue_recorded_body_work (fun _ => 1) events <= 2 * length events.
Proof.
  unfold queue_recorded_encoder_receipts, audit_queue_recorded_body_work,
    audit_queue_nested_body_work.
  intro Hall; induction Hall as [|[event [observed bodies]] rest Hreceipt Hall IH].
  - cbn; lia.
  - destruct event; cbn in Hreceipt; subst bodies;
      unfold fx_index_encoder in *; simpl in *; lia.
Qed.

Lemma fx_push_budget C (EC : encoding C) priority c queue :
  let '(_, events) := audit_queue_recorded_push (fx_index_encoder EC) priority c queue in
  1 + fx_queue_internal_charge EC events + audit_queue_recorded_body_work (fun _ => 1) events <=
    fx_declared_push_input_budget EC priority c queue.
Proof.
  pose proof (audit_queue_recorded_full_push_correct C _ EC (fx_index_encoder EC) (fun _ => 1)
    priority c queue (fx_queue_encoder_erases EC)) as Hfull.
  pose proof (queue_recorded_push_encoder_receipts C _ (fx_index_encoder EC) priority c queue)
    as Hreceipts.
  destruct (audit_queue_recorded_push (fx_index_encoder EC) priority c queue) as [out events].
  change (queue_recorded_encoder_receipts (fx_index_encoder EC) events) in Hreceipts.
  pose proof (fx_queue_body_bound C EC events Hreceipts) as Hbody.
  destruct Hfull as [_ [_ [_ [_ [Hlength Hwork]]]]].
  unfold audit_queue_recorded_full_source_work, fx_queue_internal_charge,
    fx_declared_push_input_budget in *; lia.
Qed.

Lemma fx_pop_budget C (EC : encoding C) queue :
  let '(_, events) := audit_queue_recorded_pop (fx_index_encoder EC) queue in
  1 + fx_queue_internal_charge EC events + audit_queue_recorded_body_work (fun _ => 1) events <=
    fx_declared_pop_input_budget EC queue.
Proof.
  pose proof (audit_queue_recorded_full_pop_correct C _ EC (fx_index_encoder EC) (fun _ => 1)
    queue (fx_queue_encoder_erases EC)) as Hfull.
  pose proof (queue_recorded_pop_fuel_encoder_receipts C _ (fx_index_encoder EC)
    (PQueue.pending_count queue) (PQueue.pending queue) (PQueue.live queue)
    (PQueue.live_count queue))
    as Hreceipts.
  change (queue_recorded_encoder_receipts (fx_index_encoder EC)
    (snd (audit_queue_recorded_pop (fx_index_encoder EC) queue))) in Hreceipts.
  destruct (audit_queue_recorded_pop (fx_index_encoder EC) queue) as [out events].
  change (queue_recorded_encoder_receipts (fx_index_encoder EC) events) in Hreceipts.
  pose proof (fx_queue_body_bound C EC events Hreceipts) as Hbody.
  destruct Hfull as [_ [_ [_ [_ [Hlength Hwork]]]]].
  unfold audit_queue_recorded_full_source_work, fx_queue_internal_charge,
    fx_declared_pop_input_budget in *; lia.
Qed.

Lemma fx_work_app X C A (EC : encoding C) (left right : audit_trace (fx_declared_call X C A)) :
  fx_declared_model_work EC (left ++ right) =
    fx_declared_model_work EC left + fx_declared_model_work EC right.
Proof.
  induction left as [|event rest IH]; cbn [app fx_declared_model_work]; [reflexivity|].
  destruct event as [site operands|call|site operands|bit|site operands];
    cbn [fx_declared_model_work]; rewrite IH; lia.
Qed.

Lemma fx_map_get_body_bound K V key (input : Map.t K V) :
  audit_trie_get_trace_source_work (snd (audit_map_code_get key input)) <= 5 * Pos.size_nat key.
Proof.
  pose proof (audit_trie_get_trace_adequate (K * V)%type key input) as Htrace.
  pose proof (audit_trie_get_source_work_bound (K * V)%type key input) as Hbound.
  unfold audit_map_code_get.
  destruct (audit_trie_get key input) as [out events]; cbn in Htrace |- *.
  rewrite Htrace; exact Hbound.
Qed.

Lemma fx_map_set_body_bound K V key (k : K) (value : V) (input : Map.t K V) :
  audit_trie_update_trace_source_work (snd (audit_trie_set key (k, value) input)) <=
    16 * Pos.size_nat key.
Proof.
  pose proof (audit_trie_update_trace_adequate (K * V)%type key (Some (k, value)) input) as Htrace.
  pose proof (audit_trie_update_source_work_bound (K * V)%type key (Some (k, value)) input)
    as Hbound.
  unfold audit_trie_set.
  destruct (audit_trie_update key (Some (k, value)) input) as [out events]; cbn in Htrace |- *.
  rewrite Htrace; exact Hbound.
Qed.

Section WorkBounds.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).

Lemma fx_lookup_budget values x :
  fx_declared_model_work EC (snd (@fx_model_lookup X C A EX L values x)) <=
    fx_fullcheck_lookup_input_budget EX x.
Proof.
  pose proof (fx_map_get_body_bound X A (encode EX x) values) as Hget.
  unfold fx_model_lookup; destruct (audit_map_code_get (encode EX x) values) as [raw body].
  change (audit_trie_get_trace_source_work body <= 5 * Pos.size_nat (encode EX x)) in Hget.
  destruct raw; unfold fx_fullcheck_lookup_input_budget, fx_declared_model_work,
    fx_declared_call_charge, audit_encoding_weight, audit_get_weight, audit_key_bits_weight;
    cbn; lia.
Qed.

Lemma fx_query_budget q values :
  fx_declared_model_work EC (snd (@fx_model_query X C A EX L q values)) <=
    fx_fullcheck_query_input_budget EX L values q.
Proof.
  induction q as [a|x k IH|x a q IH].
  - reflexivity.
  - pose proof (fx_lookup_budget values x) as Hlookup.
    pose proof (@fx_lookup_erases X C A EX L values x) as Herases.
    destruct (fx_model_lookup EX L values x) as [value lookup_events] eqn:Hlookup_run.
    change (fx_declared_model_work EC lookup_events <= fx_fullcheck_lookup_input_budget EX x)
      in Hlookup.
    change (value = lookup EX L values x) in Herases; subst value.
    specialize (IH (lookup EX L values x)).
    destruct (fx_model_query EX L (k (lookup EX L values x)) values)
      as [[[v reads] sides] body] eqn:Hquery.
    change (fx_declared_model_work EC body <= fx_fullcheck_query_input_budget EX L values
      (k (lookup EX L values x))) in IH.
    cbn [fx_model_query fx_fullcheck_query_input_budget]; rewrite Hlookup_run, Hquery; cbn.
    repeat rewrite fx_work_app; cbn [fx_declared_model_work fx_declared_call_charge];
      repeat rewrite fx_work_app; cbn [fx_declared_model_work];
      unfold fx_fullcheck_lookup_input_budget in Hlookup; lia.
  - destruct (fx_model_query EX L q values) as [[[v reads] sides] body] eqn:Hquery.
    change (fx_declared_model_work EC body <= fx_fullcheck_query_input_budget EX L values q) in IH.
    cbn [fx_model_query fx_fullcheck_query_input_budget]; rewrite Hquery; cbn.
    repeat rewrite fx_work_app; cbn [fx_declared_model_work];
      repeat rewrite fx_work_app; cbn [fx_declared_model_work]; lia.
Qed.

Lemma fx_enqueue_budget cs queue :
  fx_declared_model_work EC (snd (@fx_model_enqueue X C A EC sch S cs queue)) <=
    fx_declared_enqueue_input_budget EC sch S cs queue.
Proof.
  revert queue; induction cs as [|c rest IH]; intro queue.
  - reflexivity.
  - pose proof (fx_push_budget C EC (priority sch (System.target S c)) c queue) as Hpush.
    pose proof (proj1 audit_queue_recorded_holds C _ EC (fx_index_encoder EC)
      (priority sch (System.target S c)) c queue (fx_queue_encoder_erases EC)) as Herases.
    destruct (audit_queue_recorded_push (fx_index_encoder EC)
      (priority sch (System.target S c)) c queue) as [next body] eqn:Hpush_run.
    lazy beta iota zeta in Hpush, Herases; destruct Herases as [Herases _].
    specialize (IH next).
    destruct (fx_model_enqueue EC sch S rest next) as [out tail] eqn:Htail.
    change (fx_declared_model_work EC tail <= fx_declared_enqueue_input_budget EC sch S rest next)
      in IH.
    unfold fx_model_enqueue at 1; rewrite Hpush_run.
    change (fx_declared_model_work EC (snd (let '(out, tail) :=
      fx_model_enqueue EC sch S rest next in (out, [AuditCase 2 [];
      AuditCall (FxTarget c (System.target S c));
      AuditCall (FxPriority (System.target S c) (priority sch (System.target S c)));
      AuditCall (FxPush (priority sch (System.target S c)) c queue next body)] ++ tail))) <=
      fx_declared_enqueue_input_budget EC sch S (c :: rest) queue).
    rewrite Htail; cbn [snd].
    cbn [fx_declared_model_work fx_declared_call_charge].
    cbn [fx_declared_enqueue_input_budget]; rewrite <- Herases.
    rewrite fx_work_app; cbn [fx_declared_model_work fx_declared_call_charge]; lia.
Qed.

Lemma fx_raise_budget x old value :
  fx_declared_model_work EC (snd (@fx_model_raise X C A L sch mode x old value)) <= 4.
Proof.
  destruct mode; unfold fx_model_raise; try destruct (widening_point sch x);
    cbn; unfold fx_declared_model_work, fx_declared_call_charge; cbn; lia.
Qed.

Lemma fx_update_budget xa mq :
  fx_declared_model_work EC (snd (fx_model_update EX EC L sch mode S ix xa mq)) <=
    fx_declared_update_input_budget EX EC L sch mode S ix xa mq.
Proof.
  destruct xa as [x value], mq as [values queue].
  pose proof (fx_lookup_budget values x) as Hlookup.
  pose proof (@fx_lookup_erases X C A EX L values x) as Hlookup_erases.
  destruct (fx_model_lookup EX L values x) as [old lookup_events] eqn:Hlookup_run.
  change (fx_declared_model_work EC lookup_events <= fx_fullcheck_lookup_input_budget EX x)
    in Hlookup.
  change (old = lookup EX L values x) in Hlookup_erases; subst old.
  unfold fx_model_update, fx_declared_update_input_budget; rewrite Hlookup_run.
  destruct (leb L value (lookup EX L values x)) eqn:Hleb.
  - cbn; rewrite fx_work_app; cbn [fx_declared_model_work fx_declared_call_charge].
    unfold fx_fullcheck_lookup_input_budget in Hlookup; lia.
  - pose proof (fx_raise_budget x (lookup EX L values x) value) as Hraise.
    destruct (@fx_model_raise X C A L sch mode x (lookup EX L values x) value)
      as [raised raise_events] eqn:Hraise_run.
    change (fx_declared_model_work EC raise_events <= 4) in Hraise.
    pose proof (fx_map_set_body_bound X A (encode EX x) x raised values) as Hset.
    destruct (audit_trie_set (encode EX x) (x, raised) values) as [next_values write_body].
    change (audit_trie_update_trace_source_work write_body <= 16 * Pos.size_nat (encode EX x))
      in Hset.
    pose proof (fx_map_get_body_bound X (list C) (encode EX x) (readers ix)) as Hread.
    pose proof (audit_map_code_get_erases X (list C) (encode EX x) (readers ix)) as Hread_erases.
    destruct (audit_map_code_get (encode EX x) (readers ix)) as [raw read_body].
    change (audit_trie_get_trace_source_work read_body <= 5 * Pos.size_nat (encode EX x)) in Hread.
    change (raw = Map.get EX x (readers ix)) in Hread_erases.
    pose proof (fx_enqueue_budget (match raw with
      | Some cs =>
        cs
      | None =>
        []
      end) queue)
      as Henqueue.
    destruct (fx_model_enqueue EC sch S (match raw with
      | Some cs =>
        cs
      | None =>
        []
      end) queue)
      as [next_queue enqueue_events].
    change (fx_declared_model_work EC enqueue_events <= fx_declared_enqueue_input_budget EC sch S
      (match raw with
      | Some cs =>
        cs
      | None =>
        []
      end) queue) in Henqueue.
    change (fx_declared_model_work EC (lookup_events ++
      [AuditCall (FxLeb value (lookup EX L values x) false); AuditCase 4 []] ++ raise_events ++
      [AuditCall (FxSet x (encode EX x) raised values next_values write_body);
       AuditCall (FxReaders x (encode EX x) (readers ix) raw read_body); AuditCase 5 []] ++
      enqueue_events) <= fx_fullcheck_lookup_input_budget EX x + 2 +
      (6 + (2 + 19 * Pos.size_nat (encode EX x)) + (2 + 7 * Pos.size_nat (encode EX x)) +
      fx_declared_enqueue_input_budget EC sch S (readers_of EX ix x) queue)).
    unfold readers_of, index_get; rewrite <- Hread_erases.
    repeat rewrite fx_work_app; cbn [fx_declared_model_work fx_declared_call_charge].
    repeat rewrite fx_work_app; cbn [fx_declared_model_work fx_declared_call_charge].
    unfold audit_encoding_weight, audit_get_weight, audit_set_weight, audit_key_bits_weight; lia.
Qed.

Lemma fx_updates_budget updates mq :
  fx_declared_model_work EC (snd (fx_model_updates EX EC L sch mode S ix updates mq)) <=
    fx_declared_updates_input_budget EX EC L sch mode S SS ix updates mq.
Proof.
  revert mq; induction updates as [|update rest IH]; intro mq.
  - reflexivity.
  - pose proof (fx_update_budget update mq) as Hhead.
    pose proof (fx_update_erases EX EC L sch mode S SS ix update mq) as Herases.
    destruct (fx_model_update EX EC L sch mode S ix update mq) as [next head] eqn:Hhead_run.
    change (fx_declared_model_work EC head <=
      fx_declared_update_input_budget EX EC L sch mode S ix update mq) in Hhead.
    change (next = engine_update EX EC L sch mode S (Declared SS ix) Map.empty update mq)
      in Herases.
    specialize (IH next).
    destruct (fx_model_updates EX EC L sch mode S ix rest next) as [out tail] eqn:Htail.
    change (fx_declared_model_work EC tail <=
      fx_declared_updates_input_budget EX EC L sch mode S SS ix rest next) in IH.
    unfold fx_model_updates at 1; rewrite Hhead_run.
    change (fx_declared_model_work EC (snd (let '(out, tail) :=
      fx_model_updates EX EC L sch mode S ix rest next in
      (out, [AuditCase 6 []] ++ head ++ tail))) <=
      fx_declared_updates_input_budget EX EC L sch mode S SS ix (update :: rest) mq).
    rewrite Htail; cbn [snd].
    cbn [fx_declared_updates_input_budget]; rewrite <- Herases.
    repeat rewrite fx_work_app; cbn [fx_declared_model_work]; lia.
Qed.

Lemma fx_step_budget state :
  fx_declared_model_work EC (snd (fx_model_step EX EC L sch mode S ix state)) <=
    fx_declared_step_input_budget EX EC L sch mode S SS ix state.
Proof.
  pose proof (fx_pop_budget C EC (Engine.queue state)) as Hpop.
  pose proof (proj2 audit_queue_recorded_holds C _ EC (fx_index_encoder EC)
    (Engine.queue state) (fx_queue_encoder_erases EC)) as Herases.
  destruct (audit_queue_recorded_pop (fx_index_encoder EC) (Engine.queue state))
    as [popped pop_events] eqn:Hpop_run.
  lazy beta iota zeta in Hpop, Herases; destruct Herases as [Herases _].
  unfold fx_model_step, fx_declared_step_input_budget; rewrite Hpop_run, <- Herases.
  destruct popped as [[[priority c] queue]|].
  - pose proof (fx_query_budget (System.rhs S c) (Engine.current state)) as Hquery.
    pose proof (@fx_query_erases X C A EX L (System.rhs S c) (Engine.current state))
      as Hquery_erases.
    destruct (fx_model_query EX L (System.rhs S c) (Engine.current state))
      as [[[value reads] sides] query_events] eqn:Hquery_run.
    change (fx_declared_model_work EC query_events <=
      fx_fullcheck_query_input_budget EX L (Engine.current state) (System.rhs S c)) in Hquery.
    change ((value, reads, sides) = Query.run (System.rhs S c)
      (lookup EX L (Engine.current state))) in Hquery_erases.
    pose proof (fx_updates_budget ((System.target S c, value) :: sides)
      (Engine.current state, queue)) as Hupdates.
    destruct (fx_model_updates EX EC L sch mode S ix ((System.target S c, value) :: sides)
      (Engine.current state, queue)) as [[values next_queue] update_events] eqn:Hupdates_run.
    change (fx_declared_model_work EC update_events <= fx_declared_updates_input_budget EX EC L
      sch mode S SS ix ((System.target S c, value) :: sides) (Engine.current state, queue))
      in Hupdates.
    rewrite <- Hquery_erases.
    change (fx_declared_model_work EC
      ([AuditCall (FxPop (Engine.queue state) (Some (priority, c, queue)) pop_events);
        AuditCase 7 []; AuditCall (FxRhs c (System.rhs S c))] ++ query_events ++
       [AuditCall (FxTarget c (System.target S c))] ++ update_events ++
       [AuditConstruct 2 []]) <=
      fx_declared_pop_input_budget EC (Engine.queue state) + 1 +
      (3 + fx_fullcheck_query_input_budget EX L (Engine.current state) (System.rhs S c) +
       fx_declared_updates_input_budget EX EC L sch mode S SS ix
         ((System.target S c, value) :: sides) (Engine.current state, queue))).
    repeat rewrite fx_work_app; cbn [fx_declared_model_work fx_declared_call_charge].
    repeat rewrite fx_work_app; cbn [fx_declared_model_work fx_declared_call_charge]; lia.
  - change (1 + fx_queue_internal_charge EC pop_events +
      audit_queue_recorded_body_work (fun _ => 1) pop_events + 1 <=
      fx_declared_pop_input_budget EC (Engine.queue state) + 1 + 0).
    lia.
Qed.

Lemma fx_loop_budget fuel state :
  fx_declared_model_work EC (snd (fx_model_loop EX EC L sch mode S ix fuel state)) <=
    fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel state.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    pose proof (fx_loop_erases EX EC L sch mode S SS ix fuel state) as Hfirst_erases.
    destruct (fx_model_loop EX EC L sch mode S ix fuel state) as [first first_events]
      eqn:Hfirst_run.
    change (fx_declared_model_work EC first_events <=
      fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel state) in Hfirst.
    change (first = loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel state)
      in Hfirst_erases.
    unfold fx_model_loop at 1.
    fold (fx_model_loop EX EC L sch mode S ix fuel state); rewrite Hfirst_run.
    cbn [fx_declared_loop_input_budget]; rewrite <- Hfirst_erases.
    destruct first as [values|next].
    + cbn; rewrite fx_work_app; cbn [fx_declared_model_work]; lia.
    + pose proof (IH next) as Hsecond.
      pose proof (fx_loop_erases EX EC L sch mode S SS ix fuel next) as Hsecond_erases.
      destruct (fx_model_loop EX EC L sch mode S ix fuel next) as [second second_events]
        eqn:Hsecond_run.
      change (fx_declared_model_work EC second_events <=
        fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel next) in Hsecond.
      change (second = loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel next)
        in Hsecond_erases.
      fold (fx_model_loop EX EC L sch mode S ix fuel next); rewrite Hsecond_run.
      rewrite <- Hsecond_erases; destruct second as [values|last].
      * cbn; repeat rewrite fx_work_app; cbn [fx_declared_model_work].
        repeat rewrite fx_work_app; cbn [fx_declared_model_work]; lia.
      * pose proof (fx_step_budget last) as Hstep.
        destruct (fx_model_step EX EC L sch mode S ix last) as [out events] eqn:Hstep_run.
        change (fx_declared_model_work EC events <=
          fx_declared_step_input_budget EX EC L sch mode S SS ix last) in Hstep.
        change (1 + fx_declared_model_work EC (first_events ++
          (AuditCase 9 [] :: second_events) ++ [AuditCase 9 []] ++ events) <=
          3 + fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel state +
          fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel next +
          fx_declared_step_input_budget EX EC L sch mode S SS ix last).
        repeat rewrite fx_work_app.
        change (1 + (fx_declared_model_work EC first_events +
          (1 + fx_declared_model_work EC second_events + (1 + fx_declared_model_work EC events))) <=
          3 + fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel state +
          fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel next +
          fx_declared_step_input_budget EX EC L sch mode S SS ix last).
        lia.
  - pose proof (IH state) as Hfirst.
    pose proof (fx_loop_erases EX EC L sch mode S SS ix fuel state) as Hfirst_erases.
    destruct (fx_model_loop EX EC L sch mode S ix fuel state) as [first first_events]
      eqn:Hfirst_run.
    change (fx_declared_model_work EC first_events <=
      fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel state) in Hfirst.
    change (first = loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel state)
      in Hfirst_erases.
    unfold fx_model_loop at 1.
    fold (fx_model_loop EX EC L sch mode S ix fuel state); rewrite Hfirst_run.
    cbn [fx_declared_loop_input_budget]; rewrite <- Hfirst_erases.
    destruct first as [values|next].
    + cbn; rewrite fx_work_app; cbn [fx_declared_model_work]; lia.
    + pose proof (IH next) as Hsecond.
      destruct (fx_model_loop EX EC L sch mode S ix fuel next) as [out events] eqn:Hsecond_run.
      change (fx_declared_model_work EC events <=
        fx_declared_loop_input_budget EX EC L sch mode S SS ix fuel next) in Hsecond.
      fold (fx_model_loop EX EC L sch mode S ix fuel next); rewrite Hsecond_run.
      cbn; repeat rewrite fx_work_app; cbn [fx_declared_model_work].
      repeat rewrite fx_work_app; cbn [fx_declared_model_work]; lia.
  - pose proof (fx_step_budget state) as Hstep.
    destruct (fx_model_step EX EC L sch mode S ix state) as [out events] eqn:Hstep_run.
    change (fx_declared_model_work EC events <=
      fx_declared_step_input_budget EX EC L sch mode S SS ix state) in Hstep.
    unfold fx_model_loop at 1; rewrite Hstep_run.
    cbn [fx_declared_loop_input_budget].
    change (1 + fx_declared_model_work EC events <=
      1 + fx_declared_step_input_budget EX EC L sch mode S SS ix state); lia.
Qed.

End WorkBounds.

(** The complete declared run is bounded by the input and intermediate-state recurrence. *)
Theorem fx_declared_run_input_bound : fx_declared_run_input_bound_statement.
Proof.
  intros X C A EX EC L sch mode S SS ix fuel.
  pose proof (fx_run_erases EX EC L sch mode S SS ix fuel) as Herases.
  pose proof (@fx_enqueue_budget X C A EC sch S (System.constraints S) PQueue.empty)
    as Hinit.
  pose proof (fx_enqueue_erases EC sch S (System.constraints S) PQueue.empty) as Hinit_erases.
  destruct (fx_model_enqueue EC sch S (System.constraints S) PQueue.empty) as [queue init_events]
    eqn:Hinit_run.
  change (fx_declared_model_work EC init_events <=
    fx_declared_enqueue_input_budget EC sch S (System.constraints S) PQueue.empty) in Hinit.
  change (queue = enqueue EC sch S (System.constraints S) PQueue.empty) in Hinit_erases.
  pose proof (fx_loop_budget EX EC L sch mode S SS ix fuel (Engine.State Map.empty queue Map.empty))
    as Hloop.
  destruct (fx_model_loop EX EC L sch mode S ix fuel (Engine.State Map.empty queue Map.empty))
    as [out events] eqn:Hloop_run.
  change (fx_declared_model_work EC events <= fx_declared_loop_input_budget EX EC L sch mode S SS ix
    fuel (Engine.State Map.empty queue Map.empty)) in Hloop.
  unfold run_worklist_declared_model in *; rewrite Hinit_run, Hloop_run in *.
  destruct out; cbn in Herases |- *; split; [exact Herases| |exact Herases|].
  all: unfold fx_declared_run_input_budget; rewrite <- Hinit_erases.
  all: repeat rewrite fx_work_app; cbn [fx_declared_model_work];
    repeat rewrite fx_work_app; cbn [fx_declared_model_work]; lia.
Qed.
