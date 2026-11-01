(** * Declared worklist model adequacy

    The declared model follows the same worklist operations as the source engine.
    For example, a lookup retains the source's bottom result when the map has no entry.
    Builds on: FixpointAuditWorklist, CollectionsAuditTrieAdequacy and queue adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsHeap
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditTrieAdequacy CollectionsAuditQueue
  CollectionsAuditQueueAdequacy.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointTotal FixpointAuditWorklist FixpointAuditContractClosures.
Import List.ListNotations.

(** * Erasure of the modeled operations *)

Section Erasure.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A).
Context (SS : System.static S) (ix : sys_index X C).

Lemma fx_lookup_erases values x :
  fst (@fx_model_lookup X C A EX L values x) = lookup EX L values x.
Proof.
  unfold fx_model_lookup, lookup, Map.get.
  pose proof (audit_map_code_get_erases X A (encode EX x) values) as Hget.
  destruct (audit_map_code_get (encode EX x) values) as [raw body].
  cbn in Hget; now rewrite Hget.
Qed.

Lemma fx_query_erases q values :
  fst (@fx_model_query X C A EX L q values) = Query.run q (lookup EX L values).
Proof.
  induction q as [a|x k IH|x a q IH]; cbn [fx_model_query Query.run].
  - reflexivity.
  - pose proof (fx_lookup_erases values x) as Hlookup.
    destruct (fx_model_lookup EX L values x) as [value events] eqn:Hrun.
    cbn in Hlookup; subst value.
    specialize (IH (lookup EX L values x)).
    destruct (fx_model_query EX L (k (lookup EX L values x)) values) as [[[v reads] sides] body]
      eqn:Hquery.
    cbn in IH; rewrite <- IH; reflexivity.
  - destruct (fx_model_query EX L q values) as [[[v reads] sides] body] eqn:Hquery.
    cbn in IH; rewrite <- IH; reflexivity.
Qed.

Lemma fx_queue_encoder_erases : audit_queue_encoder_erases EC (fx_index_encoder EC).
Proof.
  intro c; reflexivity.
Qed.

Lemma fx_enqueue_erases cs queue :
  fst (@fx_model_enqueue X C A EC sch S cs queue) = enqueue EC sch S cs queue.
Proof.
  revert queue; induction cs as [|c rest IH]; intro queue.
  - reflexivity.
  - pose proof (proj1 audit_queue_recorded_holds C _ EC (fx_index_encoder EC)
      (priority sch (System.target S c)) c queue fx_queue_encoder_erases) as Hpush.
    destruct (audit_queue_recorded_push (fx_index_encoder EC)
      (priority sch (System.target S c)) c queue) as [next events] eqn:Hrun.
    lazy beta iota zeta in Hpush; destruct Hpush as [Hnext _].
    unfold fx_model_enqueue at 1.
    rewrite Hrun.
    change (fst (let '(out, tail) := fx_model_enqueue EC sch S rest next in
      (out, [AuditCase 2 []; AuditCall (FxTarget c (System.target S c));
        AuditCall (FxPriority (System.target S c) (priority sch (System.target S c)));
        AuditCall (FxPush (priority sch (System.target S c)) c queue next events)] ++ tail)) =
      enqueue EC sch S rest (PQueue.push EC (priority sch (System.target S c)) c queue)).
    destruct (fx_model_enqueue EC sch S rest next) as [out tail] eqn:Htail.
    specialize (IH next); rewrite Htail in IH.
    change (out = enqueue EC sch S rest next) in IH.
    change (out = enqueue EC sch S rest (PQueue.push EC
      (priority sch (System.target S c)) c queue)).
    now rewrite IH, Hnext.
Qed.

Lemma fx_raise_erases x old value :
  fst (@fx_model_raise X C A L sch mode x old value) = update_value L sch mode x old value.
Proof.
  destruct mode; cbn [fx_model_raise update_value];
    try destruct (widening_point sch x); reflexivity.
Qed.

Lemma fx_update_erases xa mq :
  fst (fx_model_update EX EC L sch mode S ix xa mq) =
    engine_update EX EC L sch mode S (Declared SS ix) Map.empty xa mq.
Proof.
  destruct xa as [x value], mq as [values queue].
  pose proof (fx_lookup_erases values x) as Hlookup.
  destruct (fx_model_lookup EX L values x) as [old lookup_events] eqn:Hlookup_run.
  change (old = lookup EX L values x) in Hlookup; subst old.
  unfold fx_model_update, engine_update; rewrite Hlookup_run.
  destruct (leb L value (lookup EX L values x)) eqn:Hleb.
  - reflexivity.
  - pose proof (fx_raise_erases x (lookup EX L values x) value) as Hraise.
    destruct (@fx_model_raise X C A L sch mode x (lookup EX L values x) value)
      as [raised raise_events] eqn:Hraise_run.
    change (raised = update_value L sch mode x (lookup EX L values x) value) in Hraise.
    pose proof (audit_trie_set_erases (X * A)%type (encode EX x) (x, raised) values) as Hset.
    destruct (audit_trie_set (encode EX x) (x, raised) values) as [next_values write_body]
      eqn:Hset_run.
    change (next_values = Map.set EX x raised values) in Hset.
    pose proof (audit_map_code_get_erases X (list C) (encode EX x) (readers ix)) as Hread.
    destruct (audit_map_code_get (encode EX x) (readers ix)) as [raw read_body] eqn:Hread_run.
    change (raw = Map.get EX x (readers ix)) in Hread.
    pose proof (fx_enqueue_erases (match raw with
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
      as [next_queue enqueue_events] eqn:Henqueue_run.
    change (next_queue = enqueue EC sch S (match raw with
      | Some cs =>
        cs
      | None =>
        []
      end) queue)
      in Henqueue.
    change ((next_values, next_queue) =
      (Map.set EX x (update_value L sch mode x (lookup EX L values x) value) values,
       enqueue EC sch S (readers_of EX ix x) queue)).
    unfold readers_of, index_get; rewrite <- Hread, <- Henqueue, <- Hraise, <- Hset.
    reflexivity.
Qed.

Lemma fx_updates_erases updates mq recorded :
  fst (fx_model_updates EX EC L sch mode S ix updates mq) =
    engine_updates EX EC L sch mode S (Declared SS ix) recorded updates mq.
Proof.
  revert mq; induction updates as [|update rest IH]; intro mq.
  - reflexivity.
  - pose proof (fx_update_erases update mq) as Hupdate.
    destruct (fx_model_update EX EC L sch mode S ix update mq) as [next head] eqn:Hhead.
    change (next = engine_update EX EC L sch mode S (Declared SS ix) Map.empty update mq)
      in Hupdate.
    assert (Hrecorded : engine_update EX EC L sch mode S (Declared SS ix) recorded update mq =
      engine_update EX EC L sch mode S (Declared SS ix) Map.empty update mq).
    { destruct update, mq; reflexivity. }
    unfold fx_model_updates at 1; rewrite Hhead.
    change (fst (let '(out, tail) := fx_model_updates EX EC L sch mode S ix rest next in
      (out, [AuditCase 6 []] ++ head ++ tail)) =
      engine_updates EX EC L sch mode S (Declared SS ix) recorded rest
        (engine_update EX EC L sch mode S (Declared SS ix) recorded update mq)).
    destruct (fx_model_updates EX EC L sch mode S ix rest next) as [out tail] eqn:Htail.
    specialize (IH next); rewrite Htail in IH.
    change (out = engine_updates EX EC L sch mode S (Declared SS ix) recorded rest next) in IH.
    change (out = engine_updates EX EC L sch mode S (Declared SS ix) recorded rest
      (engine_update EX EC L sch mode S (Declared SS ix) recorded update mq)).
    now rewrite Hrecorded, <- Hupdate.
Qed.

Lemma fx_step_erases state :
  fst (fx_model_step EX EC L sch mode S ix state) =
    step_outcome EX EC L sch mode S (Declared SS ix) state.
Proof.
  pose proof (proj2 audit_queue_recorded_holds C _ EC (fx_index_encoder EC)
    (Engine.queue state) fx_queue_encoder_erases) as Hpop.
  destruct (audit_queue_recorded_pop (fx_index_encoder EC) (Engine.queue state))
    as [popped events] eqn:Hpop_run.
  lazy beta iota zeta in Hpop; destruct Hpop as [Hpop _].
  unfold fx_model_step; rewrite Hpop_run.
  unfold step_outcome, engine_step; rewrite <- Hpop.
  destruct popped as [[[priority c] queue]|].
  - pose proof (fx_query_erases (System.rhs S c) (Engine.current state)) as Hquery.
    destruct (fx_model_query EX L (System.rhs S c) (Engine.current state))
      as [[[value reads] sides] query_events] eqn:Hquery_run.
    change ((value, reads, sides) = Query.run (System.rhs S c)
      (lookup EX L (Engine.current state))) in Hquery.
    rewrite <- Hquery.
    pose proof (fx_updates_erases ((System.target S c, value) :: sides)
      (Engine.current state, queue) (Engine.recorded state)) as Hupdates.
    destruct (fx_model_updates EX EC L sch mode S ix ((System.target S c, value) :: sides)
      (Engine.current state, queue)) as [[values next_queue] update_events] eqn:Hupdates_run.
    change ((values, next_queue) = engine_updates EX EC L sch mode S (Declared SS ix)
      (Engine.recorded state) ((System.target S c, value) :: sides)
      (Engine.current state, queue)) in Hupdates.
    rewrite <- Hupdates; reflexivity.
  - reflexivity.
Qed.

Lemma fx_loop_erases fuel state :
  fst (fx_model_loop EX EC L sch mode S ix fuel state) =
    loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel state.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - specialize (IH state) as Hfirst.
    destruct (fx_model_loop EX EC L sch mode S ix fuel state) as [first first_events]
      eqn:Hfirst_run.
    change (first = loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel state)
      in Hfirst.
    cbn [fx_model_loop loop]; rewrite Hfirst_run, <- Hfirst.
    destruct first as [values|next].
    + reflexivity.
    + specialize (IH next) as Hsecond.
      destruct (fx_model_loop EX EC L sch mode S ix fuel next) as [second second_events]
        eqn:Hsecond_run.
      change (second = loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel next)
        in Hsecond.
      cbn [then_run]; rewrite <- Hsecond; destruct second as [values|last].
      * reflexivity.
      * pose proof (fx_step_erases last) as Hstep.
        destruct (fx_model_step EX EC L sch mode S ix last) as [out events] eqn:Hstep_run.
        change (out = step_outcome EX EC L sch mode S (Declared SS ix) last) in Hstep.
        cbn [then_run]; rewrite <- Hstep; reflexivity.
  - specialize (IH state) as Hfirst.
    destruct (fx_model_loop EX EC L sch mode S ix fuel state) as [first first_events]
      eqn:Hfirst_run.
    change (first = loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel state)
      in Hfirst.
    cbn [fx_model_loop loop]; rewrite Hfirst_run, <- Hfirst.
    destruct first as [values|next].
    + reflexivity.
    + specialize (IH next) as Hsecond.
      destruct (fx_model_loop EX EC L sch mode S ix fuel next) as [out events] eqn:Hsecond_run.
      change (out = loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel next) in Hsecond.
      cbn [then_run]; rewrite <- Hsecond; reflexivity.
  - pose proof (fx_step_erases state) as Hstep.
    destruct (fx_model_step EX EC L sch mode S ix state) as [out events] eqn:Hrun.
    change (out = step_outcome EX EC L sch mode S (Declared SS ix) state) in Hstep.
    cbn [fx_model_loop loop]; rewrite Hrun; exact Hstep.
Qed.

Lemma fx_run_erases fuel :
  fst (run_worklist_declared_model EX EC L sch mode S ix fuel) =
    run_worklist EX EC L sch mode S (Declared SS ix) fuel.
Proof.
  pose proof (fx_enqueue_erases (System.constraints S) PQueue.empty) as Henqueue.
  destruct (fx_model_enqueue EC sch S (System.constraints S) PQueue.empty) as [queue events]
    eqn:Henqueue_run.
  change (queue = enqueue EC sch S (System.constraints S) PQueue.empty) in Henqueue.
  pose proof (fx_loop_erases fuel (Engine.State Map.empty queue Map.empty)) as Hloop.
  destruct (fx_model_loop EX EC L sch mode S ix fuel (Engine.State Map.empty queue Map.empty))
    as [out body] eqn:Hloop_run.
  change (out = loop (step_outcome EX EC L sch mode S (Declared SS ix)) fuel
    (Engine.State Map.empty queue Map.empty)) in Hloop.
  unfold run_worklist_declared_model, run_worklist, initial_state.
  rewrite Henqueue_run, <- Henqueue, Hloop_run, <- Hloop.
  destruct out; reflexivity.
Qed.

End Erasure.

(** Erasing the complete declared model recovers each corresponding source operation. *)
Theorem fx_declared_model_erasure : fx_declared_model_erasure_contract.
Proof.
  intros X C A EX EC L sch mode S SS ix.
  unfold fx_declared_model_erasure_statement.
  repeat split.
  - apply fx_lookup_erases.
  - apply fx_query_erases.
  - apply fx_enqueue_erases.
  - apply fx_raise_erases.
  - apply fx_update_erases.
  - intros updates mq; apply fx_updates_erases.
  - apply fx_step_erases.
  - apply fx_loop_erases.
  - apply fx_run_erases.
Qed.

(** * Accessibility of the declared execution *)

(** Accessibility of the source engine supplies a finite model execution. *)
Theorem fx_declared_total_engine_total : fx_declared_total_engine_total_contract.
Proof.
  intros X C A EX EC L sch mode S SS ix start Hacc.
  induction Hacc as [state Hacc IH].
  pose proof (fx_step_erases EX EC L sch mode S SS ix state) as Herases.
  destruct (fx_model_step EX EC L sch mode S ix state) as [out events] eqn:Hstep.
  change (out = step_outcome EX EC L sch mode S (Declared SS ix) state) in Herases.
  destruct out as [values|next].
  - exists values, events; constructor; exact Hstep.
  - assert (Hnext : engine_rel EX EC L sch mode S (Declared SS ix) next state).
    { unfold step_outcome in Herases; unfold engine_rel.
      destruct (engine_step EX EC L sch mode S (Declared SS ix) state) as [next'|]
        eqn:Hsource; inversion Herases; subst; reflexivity. }
    destruct (IH next Hnext) as [values [tail Hrun]].
    exists values, (events ++ tail); econstructor; eassumption.
Qed.

Lemma fx_total_run_source X C A (EX : encoding X) (EC : encoding C) (L : lattice A)
    (sch : scheduler X) mode (S : System.t X C A) (SS : System.static S) ix start values events :
  fx_declared_total_engine_run EX EC L sch mode S ix start values events ->
  exists steps final,
    engine_steps EX EC L sch mode S (Declared SS ix) steps start final /\
    engine_step EX EC L sch mode S (Declared SS ix) final = None /\
    Engine.current final = values.
Proof.
  intro Hrun; induction Hrun as
    [state result events Hstep|state next result head tail Hstep Hrun IH].
  - pose proof (fx_step_erases EX EC L sch mode S SS ix state) as Herases.
    rewrite Hstep in Herases; unfold step_outcome in Herases; cbn in Herases.
    destruct (engine_step EX EC L sch mode S (Declared SS ix) state) as [next|] eqn:Hsource;
      [discriminate|].
    inversion Herases; subst result; exists 0, state; repeat split; constructor || assumption.
  - pose proof (fx_step_erases EX EC L sch mode S SS ix state) as Herases.
    rewrite Hstep in Herases; unfold step_outcome in Herases; cbn in Herases.
    destruct (engine_step EX EC L sch mode S (Declared SS ix) state) as [source_next|]
      eqn:Hsource; [|discriminate].
    inversion Herases; subst source_next.
    destruct IH as [steps [final [Hsteps [Hnone Hcurrent]]]].
    exists (Datatypes.S steps), final; split.
    + eapply engine_steps_cons; eassumption.
    + split; assumption.
Qed.

(** The terminating total solver's returned map is produced by the same declared model. *)
Theorem total_solver_map_model_execution : total_solver_map_model_execution_statement.
Proof.
  intros X C A EX EC L HL sch mode S SS HT.
  destruct (engine_acc EX EC L S sch mode SS (index_system EX S SS) HL HT
    (index_system_laws EX S SS)) as [Hacc _].
  destruct (fx_declared_total_engine_total X C A EX EC L sch mode S SS
    (index_system EX S SS) (initial_state EC sch S) Hacc) as [values [events Hrun]].
  exists events.
  pose proof (fx_total_run_source X C A EX EC L sch mode S SS (index_system EX S SS)
    (initial_state EC sch S) values events Hrun) as Hsource.
  destruct Hsource as [n [final [Hsteps [Hnone Hcurrent]]]].
  destruct (proj2_sig (total_solver_map EX EC L HL sch mode S SS HT)) as
    [_ [k [last [Hsteps' [Hnone' Hcurrent']]]]].
  assert (Hequal : values = proj1_sig (total_solver_map EX EC L HL sch mode S SS HT)).
  { set (fuel := Pos.of_succ_nat (n + k)).
    assert (Hn : (n < Pos.to_nat fuel)%nat).
    { unfold fuel; rewrite SuccNat2Pos.id_succ; lia. }
    assert (Hk : (k < Pos.to_nat fuel)%nat).
    { unfold fuel; rewrite SuccNat2Pos.id_succ; lia. }
    assert (Hleft : run_worklist EX EC L sch mode S (Declared SS (index_system EX S SS)) fuel =
      Some values).
    { apply run_worklist_spec; exists n, final; auto. }
    assert (Hright : run_worklist EX EC L sch mode S (Declared SS (index_system EX S SS)) fuel =
      Some (proj1_sig (total_solver_map EX EC L HL sch mode S SS HT))).
    { apply run_worklist_spec; exists k, last; auto. }
    congruence. }
  now rewrite <- Hequal.
Qed.

(** * Counted probes and right-hand-side calls *)

Definition fx_auxiliary_event {X C A} (event : audit_event (fx_declared_call X C A)) : Prop :=
  match event with
  | AuditCall (FxPop _ _ _)
  | AuditCall (FxRhs _ _) =>
    False
  | _ =>
    True
  end.

Section EventCounts.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A) (ix : sys_index X C).

Lemma fx_lookup_auxiliary values x :
  Forall fx_auxiliary_event (snd (@fx_model_lookup X C A EX L values x)).
Proof.
  unfold fx_model_lookup; destruct (audit_map_code_get (encode EX x) values);
    destruct o; repeat constructor.
Qed.

Lemma fx_query_auxiliary q values :
  Forall fx_auxiliary_event (snd (@fx_model_query X C A EX L q values)).
Proof.
  induction q as [a|x k IH|x a q IH].
  - repeat constructor.
  - pose proof (fx_lookup_auxiliary values x) as Hlookup.
    destruct (fx_model_lookup EX L values x) as [value lookup_events] eqn:Hlookup_run.
    change (Forall fx_auxiliary_event lookup_events) in Hlookup.
    specialize (IH value).
    destruct (fx_model_query EX L (k value) values) as [[[v reads] sides] body] eqn:Hquery.
    change (Forall fx_auxiliary_event body) in IH.
    cbn [fx_model_query]; rewrite Hlookup_run, Hquery; cbn.
    repeat (rewrite Forall_app || split || assumption || constructor).
  - destruct (fx_model_query EX L q values) as [[[v reads] sides] body] eqn:Hquery.
    change (Forall fx_auxiliary_event body) in IH.
    cbn [fx_model_query]; rewrite Hquery; cbn.
    repeat (rewrite Forall_app || split || assumption || constructor).
Qed.

Lemma fx_enqueue_auxiliary cs queue :
  Forall fx_auxiliary_event (snd (@fx_model_enqueue X C A EC sch S cs queue)).
Proof.
  revert queue; induction cs as [|c rest IH]; intro queue.
  - repeat constructor.
  - destruct (audit_queue_recorded_push (fx_index_encoder EC)
      (priority sch (System.target S c)) c queue) as [next events] eqn:Hpush.
    specialize (IH next).
    destruct (fx_model_enqueue EC sch S rest next) as [out tail] eqn:Htail.
    change (Forall fx_auxiliary_event tail) in IH.
    unfold fx_model_enqueue at 1; rewrite Hpush.
    change (Forall fx_auxiliary_event (snd (let '(out, tail) :=
      fx_model_enqueue EC sch S rest next in (out, [AuditCase 2 [];
      AuditCall (FxTarget c (System.target S c));
      AuditCall (FxPriority (System.target S c) (priority sch (System.target S c)));
      AuditCall (FxPush (priority sch (System.target S c)) c queue next events)] ++ tail)))).
    rewrite Htail; cbn.
    repeat (rewrite Forall_app || split || assumption || constructor).
Qed.

Lemma fx_raise_auxiliary x old value :
  Forall fx_auxiliary_event (snd (@fx_model_raise X C A L sch mode x old value)).
Proof.
  destruct mode; cbn [fx_model_raise]; try destruct (widening_point sch x); repeat constructor.
Qed.

Lemma fx_update_auxiliary xa mq :
  Forall fx_auxiliary_event (snd (fx_model_update EX EC L sch mode S ix xa mq)).
Proof.
  destruct xa as [x value], mq as [values queue].
  pose proof (fx_lookup_auxiliary values x) as Hlookup.
  destruct (fx_model_lookup EX L values x) as [old lookup_events] eqn:Hlookup_run.
  change (Forall fx_auxiliary_event lookup_events) in Hlookup.
  unfold fx_model_update; rewrite Hlookup_run.
  destruct (leb L value old) eqn:Hleb.
  - cbn; apply Forall_app; split; [exact Hlookup|repeat constructor].
  - pose proof (fx_raise_auxiliary x old value) as Hraise.
    destruct (fx_model_raise L sch mode x old value) as [raised raise_events] eqn:Hraise_run.
    change (Forall fx_auxiliary_event raise_events) in Hraise.
    destruct (audit_trie_set (encode EX x) (x, raised) values) as [next_values write_body].
    destruct (audit_map_code_get (encode EX x) (readers ix)) as [raw read_body].
    pose proof (fx_enqueue_auxiliary (match raw with
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
    change (Forall fx_auxiliary_event enqueue_events) in Henqueue.
    cbn; repeat (rewrite Forall_app || split || assumption || constructor).
Qed.

Lemma fx_updates_auxiliary updates mq :
  Forall fx_auxiliary_event (snd (fx_model_updates EX EC L sch mode S ix updates mq)).
Proof.
  revert mq; induction updates as [|update rest IH]; intro mq.
  - repeat constructor.
  - pose proof (fx_update_auxiliary update mq) as Hhead.
    destruct (fx_model_update EX EC L sch mode S ix update mq) as [next head] eqn:Hhead_run.
    change (Forall fx_auxiliary_event head) in Hhead.
    specialize (IH next).
    destruct (fx_model_updates EX EC L sch mode S ix rest next) as [out tail] eqn:Htail.
    change (Forall fx_auxiliary_event tail) in IH.
    unfold fx_model_updates at 1; rewrite Hhead_run.
    change (Forall fx_auxiliary_event (snd (let '(out, tail) :=
      fx_model_updates EX EC L sch mode S ix rest next in
      (out, [AuditCase 6 []] ++ head ++ tail)))).
    rewrite Htail; cbn.
    repeat (rewrite Forall_app || split || assumption || constructor).
Qed.

End EventCounts.

Definition fx_pop_count {X C A} (events : audit_trace (fx_declared_call X C A)) : nat :=
  length (filter (fun event => match event with
    | AuditCall (FxPop _ _ _) =>
      true
    | _ =>
      false
    end) events).

Definition fx_rhs_count {X C A} (events : audit_trace (fx_declared_call X C A)) : nat :=
  length (filter (fun event => match event with
    | AuditCall (FxRhs _ _) =>
      true
    | _ =>
      false
    end) events).

Lemma fx_counts_app X C A (left right : audit_trace (fx_declared_call X C A)) :
  fx_pop_count (left ++ right) = fx_pop_count left + fx_pop_count right /\
  fx_rhs_count (left ++ right) = fx_rhs_count left + fx_rhs_count right.
Proof.
  unfold fx_pop_count, fx_rhs_count; rewrite !filter_app, !length_app; auto.
Qed.

Lemma fx_auxiliary_counts X C A (events : audit_trace (fx_declared_call X C A)) :
  Forall fx_auxiliary_event events -> fx_pop_count events = 0 /\ fx_rhs_count events = 0.
Proof.
  intro Hall; induction Hall as [|event rest Hevent Hall IH].
  - split; reflexivity.
  - destruct event as [site operands|call|site operands|bit|site operands];
      try (destruct call); cbn [fx_auxiliary_event] in Hevent; try contradiction;
      cbn [fx_pop_count fx_rhs_count] in *; destruct IH; split; assumption.
Qed.

Section StepCounts.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A) (ix : sys_index X C).

Lemma fx_step_counts state :
  let '(out, events) := fx_model_step EX EC L sch mode S ix state in
  fx_pop_count events = 1 /\
  fx_rhs_count events = match out with
    | Done _ =>
      0
    | Pending _ =>
      1
    end.
Proof.
  unfold fx_model_step.
  destruct (audit_queue_recorded_pop (fx_index_encoder EC) (Engine.queue state)) as [popped body].
  destruct popped as [[[priority c] queue]|].
  - pose proof (@fx_query_auxiliary X C A EX L (System.rhs S c) (Engine.current state)) as Hquery.
    destruct (fx_model_query EX L (System.rhs S c) (Engine.current state))
      as [[[value reads] sides] query_events].
    change (Forall fx_auxiliary_event query_events) in Hquery.
    pose proof (fx_updates_auxiliary EX EC L sch mode S ix ((System.target S c, value) :: sides)
      (Engine.current state, queue)) as Hupdates.
    destruct (fx_model_updates EX EC L sch mode S ix ((System.target S c, value) :: sides)
      (Engine.current state, queue)) as [[values next_queue] update_events].
    change (Forall fx_auxiliary_event update_events) in Hupdates.
    destruct (fx_auxiliary_counts X C A _ Hquery) as [Hqp Hqr].
    destruct (fx_auxiliary_counts X C A _ Hupdates) as [Hup Hur].
    unfold fx_pop_count, fx_rhs_count in *.
    rewrite !filter_app, !length_app; cbn; lia.
  - split; reflexivity.
Qed.

End StepCounts.

Lemma fx_work_equation X C A (EC : encoding C) (events : audit_trace (fx_declared_call X C A)) :
  fx_declared_model_work EC events = audit_work events + fx_declared_primitive_budget EC events.
Proof.
  induction events as [|event rest IH].
  - reflexivity.
  - destruct event as [site operands|call|site operands|bit|site operands];
      try destruct call; cbn [fx_declared_model_work fx_declared_primitive_budget
        fx_declared_call_charge audit_work audit_encoding_weight audit_get_weight audit_set_weight
        audit_key_bits_weight] in *;
      unfold audit_work, audit_encoding_weight, audit_get_weight, audit_set_weight,
        audit_key_bits_weight in *; cbn in *; lia.
Qed.

(** Every modeled total run has the source steps, final value, and exact probe and RHS counts. *)
Theorem fx_declared_total_engine_erases : fx_declared_total_engine_erases_contract.
Proof.
  intros X C A EX EC L sch mode S SS ix start values events Hrun.
  induction Hrun as [state result events Hstep|state next result head tail Hstep Hrun IH].
  - pose proof (fx_step_erases EX EC L sch mode S SS ix state) as Herases.
    pose proof (fx_step_counts EX EC L sch mode S ix state) as Hcounts.
    rewrite Hstep in Herases, Hcounts; cbn in Herases, Hcounts.
    unfold step_outcome in Herases.
    destruct (engine_step EX EC L sch mode S (Declared SS ix) state) as [next|] eqn:Hsource;
      [discriminate|].
    inversion Herases; subst result.
    exists 0, state; split; [constructor|].
    split; [exact Hsource|]; split; [reflexivity|].
    destruct Hcounts as [Hpop Hrhs]; repeat split; try assumption.
    apply fx_work_equation.
  - pose proof (fx_step_erases EX EC L sch mode S SS ix state) as Herases.
    pose proof (fx_step_counts EX EC L sch mode S ix state) as Hcounts.
    rewrite Hstep in Herases, Hcounts; cbn in Herases, Hcounts.
    unfold step_outcome in Herases.
    destruct (engine_step EX EC L sch mode S (Declared SS ix) state) as [source_next|]
      eqn:Hsource; [|discriminate].
    inversion Herases; subst source_next.
    destruct IH as [steps [final [Hsteps [Hnone [Hcurrent [Hpop [Hrhs Hwork]]]]]]].
    destruct Hcounts as [Hheadpop Hheadrhs].
    change (fx_pop_count tail = Datatypes.S steps) in Hpop.
    change (fx_rhs_count tail = steps) in Hrhs.
    destruct (fx_counts_app X C A head tail) as [Hpopapp Hrhsapp].
    exists (Datatypes.S steps), final; split.
    + eapply engine_steps_cons; eassumption.
    + split; [exact Hnone|]; split; [exact Hcurrent|].
      change (fx_pop_count (head ++ tail) = Datatypes.S (Datatypes.S steps) /\
        fx_rhs_count (head ++ tail) = Datatypes.S steps /\
        fx_declared_model_work EC (head ++ tail) = audit_work (head ++ tail) +
          fx_declared_primitive_budget EC (head ++ tail)).
      rewrite Hpopapp, Hrhsapp, Hheadpop, Hheadrhs, Hpop, Hrhs.
      split; [lia|]; split; [lia|apply fx_work_equation].
Qed.

Section LoopCounts.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A).
Context (sch : scheduler X) (mode : strategy) (S : System.t X C A) (ix : sys_index X C).

Lemma fx_loop_counts fuel state :
  let '(_, events) := fx_model_loop EX EC L sch mode S ix fuel state in
  fx_pop_count events <= Pos.to_nat fuel /\ fx_rhs_count events <= Pos.to_nat fuel.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    destruct (fx_model_loop EX EC L sch mode S ix fuel state) as [first first_events]
      eqn:Hfirst_run.
    change (fx_pop_count first_events <= Pos.to_nat fuel /\
      fx_rhs_count first_events <= Pos.to_nat fuel) in Hfirst.
    cbn [fx_model_loop]; rewrite Hfirst_run.
    destruct first as [values|next].
    + unfold fx_pop_count, fx_rhs_count in *; cbn.
      rewrite !filter_app, !length_app; cbn; repeat rewrite filter_app; repeat rewrite length_app;
        cbn; rewrite Pos2Nat.inj_xI; lia.
    + pose proof (IH next) as Hsecond.
      destruct (fx_model_loop EX EC L sch mode S ix fuel next) as [second second_events]
        eqn:Hsecond_run.
      change (fx_pop_count second_events <= Pos.to_nat fuel /\
        fx_rhs_count second_events <= Pos.to_nat fuel) in Hsecond.
      destruct second as [values|last].
      * unfold fx_pop_count, fx_rhs_count in *; cbn.
        rewrite !filter_app, !length_app; cbn; repeat rewrite filter_app; repeat rewrite length_app;
          cbn; rewrite Pos2Nat.inj_xI; lia.
      * pose proof (fx_step_counts EX EC L sch mode S ix last) as Hstep.
        destruct (fx_model_step EX EC L sch mode S ix last) as [out events] eqn:Hstep_run.
        destruct out as [values|last'].
        -- change (fx_pop_count events = 1 /\ fx_rhs_count events = 0) in Hstep.
           unfold fx_pop_count, fx_rhs_count in *; cbn.
           rewrite !filter_app, !length_app; cbn; repeat rewrite filter_app;
             repeat rewrite length_app; cbn; rewrite Pos2Nat.inj_xI; lia.
        -- change (fx_pop_count events = 1 /\ fx_rhs_count events = 1) in Hstep.
           unfold fx_pop_count, fx_rhs_count in *; cbn.
           rewrite !filter_app, !length_app; cbn; repeat rewrite filter_app;
             repeat rewrite length_app; cbn; rewrite Pos2Nat.inj_xI; lia.
  - pose proof (IH state) as Hfirst.
    destruct (fx_model_loop EX EC L sch mode S ix fuel state) as [first first_events]
      eqn:Hfirst_run.
    change (fx_pop_count first_events <= Pos.to_nat fuel /\
      fx_rhs_count first_events <= Pos.to_nat fuel) in Hfirst.
    cbn [fx_model_loop]; rewrite Hfirst_run.
    destruct first as [values|next].
    + unfold fx_pop_count, fx_rhs_count in *; cbn.
      rewrite !filter_app, !length_app; cbn; repeat rewrite filter_app; repeat rewrite length_app;
        cbn; rewrite Pos2Nat.inj_xO; lia.
    + pose proof (IH next) as Hsecond.
      destruct (fx_model_loop EX EC L sch mode S ix fuel next) as [out events] eqn:Hsecond_run.
      change (fx_pop_count events <= Pos.to_nat fuel /\ fx_rhs_count events <= Pos.to_nat fuel)
        in Hsecond.
      unfold fx_pop_count, fx_rhs_count in *; cbn.
      rewrite !filter_app, !length_app; cbn; repeat rewrite filter_app; repeat rewrite length_app;
        cbn; rewrite Pos2Nat.inj_xO; lia.
  - pose proof (fx_step_counts EX EC L sch mode S ix state) as Hstep.
    destruct (fx_model_step EX EC L sch mode S ix state) as [out events] eqn:Hstep_run.
    cbn [fx_model_loop]; rewrite Hstep_run.
    destruct out; cbn in Hstep |- *; unfold fx_pop_count, fx_rhs_count in *; cbn in *; lia.
Qed.

End LoopCounts.

(** The declared run preserves its result and work equation, with fuel-limited call counts. *)
Theorem run_worklist_declared_model_cost : run_worklist_declared_model_cost_contract.
Proof.
  intros X C A EX EC L sch mode S SS ix fuel.
  pose proof (fx_run_erases EX EC L sch mode S SS ix fuel) as Herases.
  pose proof (fx_enqueue_auxiliary EC sch S (System.constraints S) PQueue.empty) as Hinit.
  destruct (fx_model_enqueue EC sch S (System.constraints S) PQueue.empty) as [queue init_events]
    eqn:Hinit_run.
  change (Forall fx_auxiliary_event init_events) in Hinit.
  destruct (fx_auxiliary_counts X C A _ Hinit) as [Hinitpop Hinitrhs].
  pose proof (fx_loop_counts EX EC L sch mode S ix fuel (Engine.State Map.empty queue Map.empty))
    as Hloop.
  destruct (fx_model_loop EX EC L sch mode S ix fuel (Engine.State Map.empty queue Map.empty))
    as [out events] eqn:Hloop_run.
  change (fx_pop_count events <= Pos.to_nat fuel /\ fx_rhs_count events <= Pos.to_nat fuel)
    in Hloop.
  unfold run_worklist_declared_model in *; rewrite Hinit_run, Hloop_run in *.
  destruct out; cbn in Herases |- *.
  all: split; [exact Herases|].
  all: split; [apply fx_work_equation|].
  all: destruct Hloop as [Hpop Hrhs];
    unfold fx_pop_count, fx_rhs_count in *;
    rewrite !filter_app, !length_app; cbn;
    repeat rewrite filter_app; repeat rewrite length_app; cbn; lia.
Qed.
