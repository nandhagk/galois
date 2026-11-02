(** * Nested machine adequacy

    The counted machine preserves the state transitions of nested iteration.
    For example, marking a changed value retains all enclosing component heads.
    Builds on: FixpointAuditNestedMachine and collection adequacy. *)

From Stdlib Require Import List PArith PeanoNat Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditTrieAdequacy CollectionsAuditFinSet
  CollectionsAuditFinSetAdequacy.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointWorklist
  FixpointNested FixpointAuditWorklist FixpointAuditWorklistAdequacy FixpointAuditWorklistBudget
  FixpointAuditWorklistBudgetAdequacy
  FixpointAuditNestedMachine
  FixpointAuditContractClosures.
Import List.ListNotations.

(** * Erasure of the source machine *)

Section MachineErasure.
Context {X C A : Type} (EX : encoding X) (L : lattice A)
  (plan : NestedPlan.t X C) (mode : strategy) (S : System.t X C A).

Lemma fx_nested_mark_heads_erases heads dirty :
  fst (@fx_nested_mark_heads X C A EX heads dirty) =
    fold_left (fun current h => FinSet.add EX h current) heads dirty.
Proof.
  revert dirty; induction heads as [|h rest IH]; intro dirty.
  - reflexivity.
  - cbn [fx_nested_mark_heads fold_left].
    pose proof (audit_finset_add_erases X (fx_encoder_entry X) (fx_index_encoder EX) EX h dirty
      eq_refl) as Hadd.
    destruct (audit_finset_add (fx_index_encoder EX) h dirty) as [next events]; cbn in Hadd.
    specialize (IH next).
    destruct (@fx_nested_mark_heads X C A EX rest next) as [out later]; cbn in IH.
    now rewrite IH, Hadd.
Qed.

Lemma fx_nested_mark_erases x (state : NestedState.t X C A) values :
  fst (fx_nested_mark EX plan x state values) = nested_mark EX plan x state values.
Proof.
  unfold fx_nested_mark, nested_mark, index_get, Map.get.
  pose proof (audit_map_code_get_erases X (list X) (encode EX x) (NestedPlan.members plan)) as Hget.
  destruct (audit_map_code_get (encode EX x) (NestedPlan.members plan)) as [raw body]; cbn in Hget.
  pose proof (fx_nested_mark_heads_erases (
    match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as Hheads.
  destruct (fx_nested_mark_heads EX (
    match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as [dirty events]; cbn in Hheads.
  now rewrite Hheads, Hget.
Qed.

Lemma fx_nested_raise_erases x old value :
  fst (fx_nested_raise EX L plan mode x old value) =
    update_value L (nested_scheduler EX plan) mode x old value.
Proof.
  unfold fx_nested_raise; destruct mode; [reflexivity|].
  pose proof (audit_finset_mem_erases X (fx_encoder_entry X) (fx_index_encoder EX) EX x
    (NestedPlan.heads plan) eq_refl) as Hmem.
  destruct (audit_finset_mem (fx_index_encoder EX) x (NestedPlan.heads plan)) as [head events].
  cbn in Hmem; destruct head.
  - change (widen L old value = if FinSet.mem EX x (NestedPlan.heads plan)
      then widen L old value else join L old value); now rewrite <- Hmem.
  - change (join L old value = if FinSet.mem EX x (NestedPlan.heads plan)
      then widen L old value else join L old value); now rewrite <- Hmem.
Qed.

Lemma fx_nested_update_erases update state :
  fst (fx_nested_update EX L plan mode update state) = nested_update EX L plan mode update state.
Proof.
  destruct update as [x value].
  pose proof (@fx_lookup_erases X C A EX L (NestedState.current state) x) as Hlookup.
  destruct (fx_model_lookup EX L (NestedState.current state) x) as [old events] eqn:Hrun.
  change (old = lookup EX L (NestedState.current state) x) in Hlookup; subst old.
  unfold fx_nested_update, nested_update; rewrite Hrun.
  destruct (leb L value (lookup EX L (NestedState.current state) x)); [reflexivity|].
  pose proof (fx_nested_raise_erases x (lookup EX L (NestedState.current state) x) value) as Hraise.
  destruct (fx_nested_raise EX L plan mode x (lookup EX L (NestedState.current state) x)) as
    [raised raise_events]; cbn in Hraise.
  pose proof (audit_trie_set_erases (X * A)%type (encode EX x) (x, raised)
    (NestedState.current state)) as Hset.
  destruct (audit_trie_set (encode EX x) (x, raised) (NestedState.current state)) as
    [values write_events]; cbn in Hset.
  change (values = Map.set EX x raised (NestedState.current state)) in Hset.
  pose proof (fx_nested_mark_erases x state values) as Hmark.
  destruct (fx_nested_mark EX plan x state values) as [out mark_events]; cbn in Hmark.
  now rewrite Hmark, Hset, Hraise.
Qed.

Lemma fx_nested_updates_erases updates state :
  fst (fx_nested_updates EX L plan mode updates state) = nested_updates EX L plan mode updates
    state.
Proof.
  unfold nested_updates; revert state; induction updates as [|update rest IH]; intro state.
  - reflexivity.
  - cbn [fx_nested_updates fold_left].
    pose proof (fx_nested_update_erases update state) as Hupdate.
    destruct (fx_nested_update EX L plan mode update state) as [next first]; cbn in Hupdate.
    specialize (IH next).
    destruct (fx_nested_updates EX L plan mode rest next) as [out later]; cbn in IH.
    now rewrite IH, Hupdate.
Qed.

Lemma fx_nested_step_erases state :
  fst (fx_nested_step EX L plan mode S state) = nested_step EX L plan mode S state.
Proof.
  destruct state as [values ready frames dirty changed].
  destruct ready as [|c rest].
  - destruct frames as [|[code restart] frames].
    + reflexivity.
    + destruct code as [|x rest|h body rest].
      * destruct restart as [[h pass]|].
        -- pose proof (audit_finset_mem_erases X (fx_encoder_entry X) (fx_index_encoder EX)
              EX h dirty eq_refl) as Hmem.
            destruct (audit_finset_mem (fx_index_encoder EX) h dirty) as [present events] eqn:Hrun.
            cbn in Hmem.
            unfold fx_nested_step, nested_step; cbn [NestedState.current NestedState.ready
              NestedState.frames NestedState.dirty NestedState.changed NestedFrame.remaining
              NestedFrame.restart]; rewrite Hrun, <- Hmem.
            destruct present; [|reflexivity].
            pose proof (audit_finset_remove_erases X (fx_encoder_entry X) (fx_index_encoder EX)
              EX h dirty eq_refl) as Hremove.
            destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next remove_events].
            cbn in Hremove; now rewrite Hremove.
        -- destruct changed; reflexivity.
      * unfold fx_nested_step, nested_step; cbn [NestedState.current NestedState.ready
          NestedState.frames NestedState.dirty NestedState.changed NestedFrame.remaining
          NestedFrame.restart].
        pose proof (audit_map_code_get_erases X (list C) (encode EX x) (NestedPlan.targets plan))
          as Hget.
        destruct (audit_map_code_get (encode EX x) (NestedPlan.targets plan)) as [raw events]
          eqn:Hrun; cbn in Hget.
        unfold index_get, Map.get; now rewrite <- Hget.
      * pose proof (audit_finset_remove_erases X (fx_encoder_entry X) (fx_index_encoder EX)
          EX h dirty eq_refl) as Hremove.
        destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next events] eqn:Hrun.
        cbn in Hremove.
        unfold fx_nested_step, nested_step; cbn [NestedState.current NestedState.ready
          NestedState.frames NestedState.dirty NestedState.changed NestedFrame.remaining
          NestedFrame.restart]; rewrite Hrun, Hremove; reflexivity.
  - pose proof (@fx_query_erases X C A EX L (System.rhs S c) values) as Hquery.
    destruct (fx_model_query EX L (System.rhs S c) values) as [[[value reads] sides] events]
      eqn:Hrun.
    change ((value, reads, sides) = Query.run (System.rhs S c) (lookup EX L values)) in Hquery.
    unfold fx_nested_step, nested_step; cbn [NestedState.current NestedState.ready
      NestedState.frames
      NestedState.dirty NestedState.changed]; rewrite Hrun, <- Hquery.
    pose proof (fx_nested_updates_erases ((System.target S c, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as Hupdates.
    destruct (fx_nested_updates EX L plan mode ((System.target S c, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as [out update_events].
    cbn in Hupdates; now rewrite Hupdates.
Qed.

Lemma fx_nested_tick_erases result :
  fst (fx_nested_tick EX L plan mode S result) =
    nested_tick (nested_step EX L plan mode S) result.
Proof.
  destruct result as [state|values]; [|reflexivity].
  unfold fx_nested_tick, nested_tick.
  pose proof (fx_nested_step_erases state) as Hstep.
  destruct (fx_nested_step EX L plan mode S state) as [next events]; cbn in Hstep.
  now rewrite <- Hstep; destruct next.
Qed.

Lemma fx_nested_loop_erases fuel state :
  fst (fx_nested_loop EX L plan mode S fuel state) =
    nested_loop (nested_step EX L plan mode S) fuel state.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    destruct (fx_nested_loop EX L plan mode S fuel state) as [first first_events] eqn:Hrun.
    cbn in Hfirst.
    cbn [fx_nested_loop nested_loop]; rewrite Hrun, <- Hfirst.
    destruct first as [next|values].
    + pose proof (IH next) as Hsecond.
      destruct (fx_nested_loop EX L plan mode S fuel next) as [second second_events] eqn:Hnext.
      cbn in Hsecond; rewrite <- Hsecond.
      pose proof (fx_nested_tick_erases second) as Htick.
      destruct (fx_nested_tick EX L plan mode S second) as [out events]; cbn in Htick.
      exact Htick.
    + pose proof (fx_nested_tick_erases (inr values)) as Htick.
      cbn [fx_nested_tick nested_tick] in Htick; exact Htick.
  - pose proof (IH state) as Hfirst.
    destruct (fx_nested_loop EX L plan mode S fuel state) as [first first_events] eqn:Hrun.
    cbn in Hfirst.
    cbn [fx_nested_loop nested_loop]; rewrite Hrun, <- Hfirst.
    destruct first as [next|values]; [|reflexivity].
    pose proof (IH next) as Hsecond.
    destruct (fx_nested_loop EX L plan mode S fuel next) as [out events] eqn:Hnext.
    cbn in Hsecond; now rewrite <- Hsecond.
  - pose proof (fx_nested_tick_erases (inl state)) as Htick.
    cbn [fx_nested_loop nested_loop].
    destruct (fx_nested_tick EX L plan mode S (inl state)) as [out events] eqn:Hrun.
    cbn in Htick; exact Htick.
Qed.

End MachineErasure.

(** Every counted transition and binary loop erases to the native nested machine. *)
Theorem fx_nested_machine_erasure : fx_nested_machine_erasure_contract.
Proof.
  unfold fx_nested_machine_erasure_contract, fx_nested_machine_erasure_statement.
  intros X C A EX L plan mode S; repeat split; intros.
  - apply fx_nested_mark_erases.
  - apply fx_nested_raise_erases.
  - apply fx_nested_update_erases.
  - apply fx_nested_updates_erases.
  - apply fx_nested_step_erases.
  - apply fx_nested_loop_erases.
Qed.

(** * Selected-event charges *)

Definition fx_machine_event_bounded {X C A} (EX : encoding X) (EC : encoding C)
    (event : fx_nested_event X C A) : Prop :=
  fx_nested_event_work EC event <= fx_nested_event_budget EX EC event.

Lemma fx_machine_events_bound X C A (EX : encoding X) (EC : encoding C)
    (events : list (fx_nested_event X C A)) :
  Forall (fx_machine_event_bounded EX EC) events ->
  fx_nested_work EC events <= fx_nested_budget EX EC events.
Proof.
  intro Hall; induction Hall as [|event rest Hhead Htail IH].
  - reflexivity.
  - cbn [fx_nested_work fx_nested_budget].
    unfold fx_machine_event_bounded in Hhead; apply Nat.add_le_mono; assumption.
Qed.

Lemma fx_machine_query_bounded X C A (EX : encoding X) (EC : encoding C) events :
  fx_machine_event_bounded EX EC (@FxNestedQuery X C A events).
Proof.
  unfold fx_machine_event_bounded; cbn [fx_nested_event_work fx_nested_event_budget].
  rewrite fx_work_equation; apply Nat.le_refl.
Qed.

Lemma fx_machine_mem_bounded X C A (EX : encoding X) (EC : encoding C) x input :
  let '(out, body) := audit_finset_mem (fx_index_encoder EX) x input in
  fx_machine_event_bounded EX EC (@FxNestedSetMem X C A x input out body).
Proof.
  pose proof (fx_map_get_body_bound X unit (encode EX x) input) as Hget.
  unfold audit_finset_mem, fx_index_encoder.
  destruct (audit_map_code_get (encode EX x) input) as [raw trace]; cbn [snd] in Hget.
  destruct raw; unfold fx_machine_event_bounded; cbn [fx_nested_event_work fx_nested_event_budget
    audit_finset_source_work length]; lia.
Qed.

Lemma fx_machine_add_bounded X C A (EX : encoding X) (EC : encoding C) x input :
  let '(out, body) := audit_finset_add (fx_index_encoder EX) x input in
  fx_machine_event_bounded EX EC (@FxNestedSetAdd X C A x input out body).
Proof.
  pose proof (fx_map_set_body_bound X unit (encode EX x) x tt input) as Hset.
  unfold audit_finset_add, fx_index_encoder.
  destruct (audit_trie_set (encode EX x) (x, tt) input) as [out trace]; cbn [snd] in Hset.
  unfold fx_machine_event_bounded; cbn [fx_nested_event_work fx_nested_event_budget
    audit_finset_source_work length]; lia.
Qed.

Lemma fx_machine_remove_bounded X C A (EX : encoding X) (EC : encoding C) x input :
  let '(out, body) := audit_finset_remove (fx_index_encoder EX) x input in
  fx_machine_event_bounded EX EC (@FxNestedSetRemove X C A x input out body).
Proof.
  pose proof (audit_trie_update_trace_adequate (X * unit)%type (encode EX x) None input) as Htrace.
  pose proof (audit_trie_update_source_work_bound (X * unit)%type (encode EX x) None input) as
    Hbound.
  unfold audit_finset_remove, fx_index_encoder, audit_trie_remove.
  destruct (audit_trie_update (encode EX x) None input) as [out trace]; cbn [snd] in Htrace.
  unfold fx_machine_event_bounded; cbn [fx_nested_event_work fx_nested_event_budget
    audit_finset_source_work length]; lia.
Qed.

Lemma fx_machine_map_bounded X C A (EX : encoding X) (EC : encoding C) x input :
  let '(out, body) := audit_map_code_get (encode EX x) input in
  fx_machine_event_bounded EX EC (@FxNestedMapGet X C A x (encode EX x) input out body).
Proof.
  pose proof (fx_map_get_body_bound X (list X) (encode EX x) input) as Hbody.
  destruct (audit_map_code_get (encode EX x) input) as [out body]; cbn [snd] in Hbody.
  change (1 + S (Pos.size_nat (encode EX x)) + audit_trie_get_trace_source_work body <=
    2 + 6 * Pos.size_nat (encode EX x)); lia.
Qed.

Lemma fx_machine_targets_bounded X C A (EX : encoding X) (EC : encoding C) x input :
  let '(out, body) := audit_map_code_get (encode EX x) input in
  fx_machine_event_bounded EX EC (@FxNestedTargetsGet X C A x (encode EX x) input out body).
Proof.
  pose proof (fx_map_get_body_bound X (list C) (encode EX x) input) as Hbody.
  destruct (audit_map_code_get (encode EX x) input) as [out body]; cbn [snd] in Hbody.
  change (1 + S (Pos.size_nat (encode EX x)) + audit_trie_get_trace_source_work body <=
    2 + 6 * Pos.size_nat (encode EX x)); lia.
Qed.

Lemma fx_machine_write_bounded X C A (EX : encoding X) (EC : encoding C) x (value : A) input :
  let '(out, body) := audit_trie_set (encode EX x) (x, value) input in
  fx_machine_event_bounded EX EC (@FxNestedValueSet X C A x value (encode EX x) input out body).
Proof.
  pose proof (fx_map_set_body_bound X A (encode EX x) x value input) as Hbody.
  destruct (audit_trie_set (encode EX x) (x, value) input) as [out body]; cbn [snd] in Hbody.
  change (1 + S (Pos.size_nat (encode EX x)) + audit_trie_update_trace_source_work body <=
    2 + 17 * Pos.size_nat (encode EX x)); lia.
Qed.

(** Close a structural event with identical work and budget. *)
Local Ltac fx_machine_trivial :=
  unfold fx_machine_event_bounded; cbn [fx_nested_event_work fx_nested_event_budget]; lia.

Section MachineSelected.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (plan : NestedPlan.t X C) (mode : strategy) (S : System.t X C A).

Lemma fx_nested_mark_heads_bounded heads dirty :
  Forall (fx_machine_event_bounded EX EC) (snd (@fx_nested_mark_heads X C A EX heads dirty)).
Proof.
  revert dirty; induction heads as [|h rest IH]; intro dirty.
  - cbn [fx_nested_mark_heads snd]; constructor; [fx_machine_trivial|constructor].
  - cbn [fx_nested_mark_heads].
    pose proof (fx_machine_add_bounded X C A EX EC h dirty) as Hadd.
    destruct (audit_finset_add (fx_index_encoder EX) h dirty) as [next events].
    specialize (IH next); destruct (@fx_nested_mark_heads X C A EX rest next) as [out later].
    cbn [snd] in IH |- *; constructor; [fx_machine_trivial|].
    constructor; assumption.
Qed.

Lemma fx_nested_mark_bounded x (state : NestedState.t X C A) values :
  Forall (fx_machine_event_bounded EX EC) (snd (fx_nested_mark EX plan x state values)).
Proof.
  unfold fx_nested_mark.
  pose proof (fx_machine_map_bounded X C A EX EC x (NestedPlan.members plan)) as Hmap.
  destruct (audit_map_code_get (encode EX x) (NestedPlan.members plan)) as [raw body].
  pose proof (fx_nested_mark_heads_bounded (
    match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as Hheads.
  destruct (fx_nested_mark_heads EX (
    match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as [dirty events].
  cbn [snd] in Hheads |- *; constructor; [exact Hmap|].
  constructor; [fx_machine_trivial|exact Hheads].
Qed.

Lemma fx_nested_raise_bounded x old value :
  Forall (fx_machine_event_bounded EX EC) (snd (fx_nested_raise EX L plan mode x old value)).
Proof.
  unfold fx_nested_raise; destruct mode.
  - cbn [snd]; repeat constructor; fx_machine_trivial.
  - pose proof (fx_machine_mem_bounded X C A EX EC x (NestedPlan.heads plan)) as Hmem.
    destruct (audit_finset_mem (fx_index_encoder EX) x (NestedPlan.heads plan)) as [head body].
    destruct head; cbn [snd].
    + constructor; [fx_machine_trivial|]. constructor; [exact Hmem|].
      repeat constructor; fx_machine_trivial.
    + constructor; [fx_machine_trivial|]. constructor; [exact Hmem|].
      repeat constructor; fx_machine_trivial.
Qed.

Lemma fx_nested_update_bounded update state :
  Forall (fx_machine_event_bounded EX EC) (snd (fx_nested_update EX L plan mode update state)).
Proof.
  destruct update as [x value]; unfold fx_nested_update.
  destruct (fx_model_lookup EX L (NestedState.current state) x) as [old lookup_events].
  destruct (leb L value old).
  - cbn [snd]; constructor; [apply fx_machine_query_bounded|].
    repeat constructor; fx_machine_trivial.
  - pose proof (fx_nested_raise_bounded x old value) as Hraise.
    destruct (fx_nested_raise EX L plan mode x old value) as [raised raise_events].
    cbn [snd] in Hraise.
    pose proof (fx_machine_write_bounded X C A EX EC x raised (NestedState.current state)) as
      Hwrite.
    destruct (audit_trie_set (encode EX x) (x, raised) (NestedState.current state)) as
      [values body].
    pose proof (fx_nested_mark_bounded x state values) as Hmark.
    destruct (fx_nested_mark EX plan x state values) as [out mark_events]; cbn [snd] in Hmark |- *.
    constructor; [apply fx_machine_query_bounded|].
    constructor; [fx_machine_trivial|].
    constructor; [fx_machine_trivial|].
    repeat rewrite Forall_app; repeat split; try assumption.
    constructor; [exact Hwrite|constructor].
Qed.

Lemma fx_nested_updates_bounded updates state :
  Forall (fx_machine_event_bounded EX EC) (snd (fx_nested_updates EX L plan mode updates state)).
Proof.
  revert state; induction updates as [|update rest IH]; intro state.
  - cbn [fx_nested_updates snd]; constructor; [fx_machine_trivial|constructor].
  - cbn [fx_nested_updates].
    pose proof (fx_nested_update_bounded update state) as Hupdate.
    destruct (fx_nested_update EX L plan mode update state) as [next events]; cbn [snd] in Hupdate.
    specialize (IH next); destruct (fx_nested_updates EX L plan mode rest next) as [out later].
    cbn [snd] in IH |- *; constructor; [fx_machine_trivial|].
    now apply Forall_app.
Qed.

Lemma fx_nested_step_bounded state :
  Forall (fx_machine_event_bounded EX EC) (snd (fx_nested_step EX L plan mode S state)).
Proof.
  destruct state as [values ready frames dirty changed]; destruct ready as [|c rest].
  - destruct frames as [|[code restart] frames].
    + cbn [fx_nested_step snd]; repeat constructor; fx_machine_trivial.
    + destruct code as [|x rest|h body rest].
      * destruct restart as [[h pass]|].
        -- pose proof (fx_machine_mem_bounded X C A EX EC h dirty) as Hmem.
            pose proof (fx_machine_remove_bounded X C A EX EC h dirty) as Hremove.
            unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
              NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart].
            destruct (audit_finset_mem (fx_index_encoder EX) h dirty) as [present events].
            destruct present.
            ++ destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next later].
              cbn [snd app]; repeat (first [assumption | fx_machine_trivial | constructor]).
            ++ cbn [snd]; repeat (first [assumption | fx_machine_trivial | constructor]).
        -- destruct changed; cbn [fx_nested_step snd]; repeat constructor; fx_machine_trivial.
      * pose proof (fx_machine_targets_bounded X C A EX EC x (NestedPlan.targets plan)) as Hget.
        unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
          NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart].
        destruct (audit_map_code_get (encode EX x) (NestedPlan.targets plan)) as [raw body].
        cbn [snd]; repeat (first [assumption | fx_machine_trivial | constructor]).
      * pose proof (fx_machine_remove_bounded X C A EX EC h dirty) as Hremove.
        unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
          NestedState.dirty NestedState.changed NestedFrame.remaining NestedFrame.restart].
        destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next events].
        cbn [snd]; repeat (first [assumption | fx_machine_trivial | constructor]).
  - unfold fx_nested_step; cbn [NestedState.current NestedState.ready NestedState.frames
      NestedState.dirty NestedState.changed].
    destruct (fx_model_query EX L (System.rhs S c) values) as [[[value reads] sides] events].
    pose proof (fx_nested_updates_bounded ((System.target S c, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as Hupdates.
    destruct (fx_nested_updates EX L plan mode ((System.target S c, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as [out later].
    cbn [snd] in Hupdates |- *.
    constructor; [fx_machine_trivial|]. constructor; [fx_machine_trivial|].
    constructor; [apply fx_machine_query_bounded|]. constructor; [fx_machine_trivial|exact
      Hupdates].
Qed.

Lemma fx_nested_tick_bounded result :
  Forall (fx_machine_event_bounded EX EC) (snd (fx_nested_tick EX L plan mode S result)).
Proof.
  destruct result as [state|values].
  - pose proof (fx_nested_step_bounded state) as Hstep.
    unfold fx_nested_tick; destruct (fx_nested_step EX L plan mode S state) as [next events].
    cbn [snd] in Hstep; destruct next; cbn [snd].
    + constructor; [fx_machine_trivial|].
      apply Forall_app; split; [exact Hstep|constructor; [fx_machine_trivial|constructor]].
    + constructor; [fx_machine_trivial|].
      apply Forall_app; split; [exact Hstep|constructor; [fx_machine_trivial|constructor]].
  - cbn [fx_nested_tick snd]; constructor; [fx_machine_trivial|constructor].
Qed.

Lemma fx_nested_loop_bounded fuel state :
  Forall (fx_machine_event_bounded EX EC) (snd (fx_nested_loop EX L plan mode S fuel state)).
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    cbn [fx_nested_loop].
    destruct (fx_nested_loop EX L plan mode S fuel state) as [first events]; cbn [snd] in Hfirst.
    destruct first as [next|values].
    + pose proof (IH next) as Hsecond.
      destruct (fx_nested_loop EX L plan mode S fuel next) as [second later]; cbn [snd] in Hsecond.
      pose proof (fx_nested_tick_bounded second) as Htick.
      destruct (fx_nested_tick EX L plan mode S second) as [out last]; cbn [snd] in Htick |- *.
      constructor; [fx_machine_trivial|].
      repeat rewrite Forall_app; repeat split; try assumption.
      constructor; [fx_machine_trivial|exact Hsecond].
    + pose proof (fx_nested_tick_bounded (inr values)) as Htick.
      destruct (fx_nested_tick EX L plan mode S (inr values)) as [out last]; cbn [snd] in Htick |-
        *.
      constructor; [fx_machine_trivial|].
      repeat rewrite Forall_app; repeat split; try assumption.
      constructor; [fx_machine_trivial|constructor].
  - pose proof (IH state) as Hfirst.
    cbn [fx_nested_loop].
    destruct (fx_nested_loop EX L plan mode S fuel state) as [first events]; cbn [snd] in Hfirst.
    destruct first as [next|values].
    + pose proof (IH next) as Hsecond.
      destruct (fx_nested_loop EX L plan mode S fuel next) as [out later]; cbn [snd] in Hsecond |-
        *.
      constructor; [fx_machine_trivial|].
      apply Forall_app; split; [exact Hfirst|constructor; [fx_machine_trivial|exact Hsecond]].
    + cbn [snd]; constructor; [fx_machine_trivial|].
      apply Forall_app; split; [exact Hfirst|constructor; [fx_machine_trivial|constructor]].
  - pose proof (fx_nested_tick_bounded (inl state)) as Htick.
    cbn [fx_nested_loop].
    destruct (fx_nested_tick EX L plan mode S (inl state)) as [out events]; cbn [snd] in Htick |- *.
    constructor; [fx_machine_trivial|exact Htick].
Qed.

End MachineSelected.

(** The selected machine trace has the native result and accounts for each nested body. *)
Theorem fx_nested_loop_selected_cost : fx_nested_loop_selected_cost_statement.
Proof.
  intros X C A EX EC L plan mode S fuel state.
  pose proof (fx_nested_loop_erases EX L plan mode S fuel state) as Herase.
  pose proof (fx_nested_loop_bounded EX EC L plan mode S fuel state) as Hbounded.
  destruct (fx_nested_loop EX L plan mode S fuel state) as [out events].
  cbn [fst snd] in Herase, Hbounded |- *; split; [exact Herase|].
  now apply fx_machine_events_bound.
Qed.

(** * Input-derived machine bounds *)

Lemma fx_nested_work_app X C A (EC : encoding C) (left right : list (fx_nested_event X C A)) :
  fx_nested_work EC (left ++ right) = fx_nested_work EC left + fx_nested_work EC right.
Proof.
  unfold fx_nested_work; induction left as [|event rest IH]; cbn [app fold_right]; lia.
Qed.

Section MachineInput.
Context {X C A : Type} (EX : encoding X) (EC : encoding C) (L : lattice A)
  (plan : NestedPlan.t X C) (mode : strategy) (S : System.t X C A).

Lemma fx_nested_mark_heads_input_bound heads dirty :
  fx_nested_work EC (snd (@fx_nested_mark_heads X C A EX heads dirty)) <=
    fx_nested_mark_input_budget EX heads.
Proof.
  revert dirty; induction heads as [|h rest IH]; intro dirty.
  - reflexivity.
  - pose proof (fx_machine_add_bounded X C A EX EC h dirty) as Hadd.
    cbn [fx_nested_mark_heads fx_nested_mark_input_budget].
    destruct (audit_finset_add (fx_index_encoder EX) h dirty) as [next events].
    specialize (IH next).
    destruct (@fx_nested_mark_heads X C A EX rest next) as [out later].
    cbn [snd] in IH |- *; unfold fx_machine_event_bounded in Hadd.
    change (1 + fx_nested_event_work EC (@FxNestedSetAdd X C A h dirty next events) +
      fx_nested_work EC later <= 1 + (12 + 17 * Pos.size_nat (encode EX h)) +
      fx_nested_mark_input_budget EX rest).
    cbn [fx_nested_event_budget] in Hadd; lia.
Qed.

Lemma fx_nested_mark_input_bound x (state : NestedState.t X C A) values :
  fx_nested_work EC (snd (fx_nested_mark EX plan x state values)) <=
    (2 + 6 * Pos.size_nat (encode EX x)) + 1 +
      fx_nested_mark_input_budget EX (index_get EX (NestedPlan.members plan) x).
Proof.
  unfold fx_nested_mark.
  pose proof (fx_machine_map_bounded X C A EX EC x (NestedPlan.members plan)) as Hmap.
  pose proof (audit_map_code_get_erases X (list X) (encode EX x) (NestedPlan.members plan)) as Hget.
  destruct (audit_map_code_get (encode EX x) (NestedPlan.members plan)) as [raw body].
  cbn [fst] in Hget.
  pose proof (fx_nested_mark_heads_input_bound (
    match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as Hheads.
  destruct (fx_nested_mark_heads EX (
    match raw with
    | Some hs => hs
    | None => []
    end)
    (NestedState.dirty state)) as [dirty events]; cbn [snd] in Hheads |- *.
  unfold index_get, Map.get; rewrite <- Hget.
  unfold fx_machine_event_bounded in Hmap; cbn [fx_nested_event_budget] in Hmap.
  change (fx_nested_event_work EC (@FxNestedMapGet X C A x (encode EX x)
    (NestedPlan.members plan) raw body) + (1 + fx_nested_work EC events) <=
    (2 + 6 * Pos.size_nat (encode EX x)) + 1 +
    fx_nested_mark_input_budget EX (
      match raw with
      | Some hs => hs
      | None => []
      end)); lia.
Qed.

Lemma fx_nested_raise_input_bound x old value :
  fx_nested_work EC (snd (fx_nested_raise EX L plan mode x old value)) <=
    4 + (12 + 5 * Pos.size_nat (encode EX x)).
Proof.
  unfold fx_nested_raise in *; destruct mode.
  - change (2 <= 4 + (12 + 5 * Pos.size_nat (encode EX x))); lia.
  - pose proof (fx_machine_mem_bounded X C A EX EC x (NestedPlan.heads plan)) as Hmem.
    destruct (audit_finset_mem (fx_index_encoder EX) x (NestedPlan.heads plan)) as [head events].
    unfold fx_machine_event_bounded in Hmem; cbn [fx_nested_event_budget] in Hmem.
    destruct head.
    + change (1 + (fx_nested_event_work EC (@FxNestedSetMem X C A x
        (NestedPlan.heads plan) true events) + (1 + (1 + 0))) <=
        4 + (12 + 5 * Pos.size_nat (encode EX x))); lia.
    + change (1 + (fx_nested_event_work EC (@FxNestedSetMem X C A x
        (NestedPlan.heads plan) false events) + (1 + (1 + 0))) <=
        4 + (12 + 5 * Pos.size_nat (encode EX x))); lia.
Qed.

Lemma fx_nested_update_input_bound update state :
  fx_nested_work EC (snd (fx_nested_update EX L plan mode update state)) <=
    fx_nested_update_input_budget EX L plan mode update state.
Proof.
  destruct update as [x value].
  pose proof (@fx_lookup_budget X C A EX EC L (NestedState.current state) x) as Hlookup.
  pose proof (@fx_lookup_erases X C A EX L (NestedState.current state) x) as Herase.
  unfold fx_nested_update, fx_nested_update_input_budget.
  destruct (fx_model_lookup EX L (NestedState.current state) x) as [old events] eqn:Hlookup_run.
  change (fx_declared_model_work EC events <= fx_fullcheck_lookup_input_budget EX x) in Hlookup.
  change (old = lookup EX L (NestedState.current state) x) in Herase; subst old.
  destruct (leb L value (lookup EX L (NestedState.current state) x)).
  - cbn [snd].
    change (fx_declared_model_work EC events + (1 + (1 + 0)) <=
      2 + fx_fullcheck_lookup_input_budget EX x + 0); lia.
  - pose proof (fx_nested_raise_input_bound x (lookup EX L (NestedState.current state) x) value)
      as Hraise.
    destruct (fx_nested_raise EX L plan mode x (lookup EX L (NestedState.current state) x)) as
      [raised raise_events]; cbn [snd] in Hraise.
    pose proof (fx_machine_write_bounded X C A EX EC x raised (NestedState.current state)) as
      Hwrite.
    destruct (audit_trie_set (encode EX x) (x, raised) (NestedState.current state)) as
      [values write_events].
    pose proof (fx_nested_mark_input_bound x state values) as Hmark.
    destruct (fx_nested_mark EX plan x state values) as [out mark_events]; cbn [snd] in Hmark |- *.
    unfold fx_machine_event_bounded in Hwrite; cbn [fx_nested_event_budget] in Hwrite.
    repeat rewrite fx_nested_work_app.
    change (fx_declared_model_work EC events + (1 + (1 + 0)) +
      (fx_nested_work EC raise_events +
        (fx_nested_event_work EC (@FxNestedValueSet X C A x raised (encode EX x)
          (NestedState.current state) values write_events) + 0 + fx_nested_work EC mark_events)) <=
      2 + fx_fullcheck_lookup_input_budget EX x +
      (5 + (12 + 5 * Pos.size_nat (encode EX x)) + (2 + 17 * Pos.size_nat (encode EX x)) +
        (2 + 6 * Pos.size_nat (encode EX x)) +
        fx_nested_mark_input_budget EX (index_get EX (NestedPlan.members plan) x))); lia.
Qed.

Lemma fx_nested_updates_input_bound updates state :
  fx_nested_work EC (snd (fx_nested_updates EX L plan mode updates state)) <=
    fx_nested_updates_input_budget EX L plan mode updates state.
Proof.
  revert state; induction updates as [|update rest IH]; intro state.
  - reflexivity.
  - pose proof (fx_nested_update_input_bound update state) as Hfirst.
    pose proof (fx_nested_update_erases EX L plan mode update state) as Herase.
    cbn [fx_nested_updates fx_nested_updates_input_budget].
    destruct (fx_nested_update EX L plan mode update state) as [next first]; cbn [snd] in Hfirst.
    change (next = nested_update EX L plan mode update state) in Herase.
    specialize (IH next).
    destruct (fx_nested_updates EX L plan mode rest next) as [out later]; cbn [snd] in IH |- *.
    change (1 + fx_nested_work EC (first ++ later) <=
      1 + fx_nested_update_input_budget EX L plan mode update state +
        fx_nested_updates_input_budget EX L plan mode rest
          (nested_update EX L plan mode update state)).
    rewrite fx_nested_work_app, <- Herase; lia.
Qed.

Lemma fx_nested_step_input_bound state :
  fx_nested_work EC (snd (fx_nested_step EX L plan mode S state)) <=
    fx_nested_step_input_budget EX L plan mode S state.
Proof.
  destruct state as [values ready frames dirty changed]; destruct ready as [|c rest].
  - destruct frames as [|[code restart] frames].
    + reflexivity.
    + destruct code as [|x rest|h body rest].
      * destruct restart as [[h pass]|].
        -- pose proof (fx_nested_step_bounded EX EC L plan mode S
              (NestedState.Make values [] (NestedFrame.Make NestedEnd (Some (h, pass)) :: frames)
                dirty changed)) as Hselected.
            apply fx_machine_events_bound in Hselected.
            unfold fx_nested_step, fx_nested_step_input_budget in *.
            cbn [NestedState.current NestedState.ready NestedState.frames NestedState.dirty
              NestedState.changed NestedFrame.remaining NestedFrame.restart] in *.
            destruct (audit_finset_mem (fx_index_encoder EX) h dirty) as [present events].
            destruct present.
            ++ destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next later].
              cbn [snd app] in Hselected |- *; unfold fx_nested_budget in Hselected;
              cbn [app fold_right fx_nested_event_budget] in Hselected; lia.
            ++ cbn [snd app] in Hselected |- *; unfold fx_nested_budget in Hselected;
              cbn [app fold_right fx_nested_event_budget] in Hselected; lia.
        -- destruct changed; change (5 <= 6); lia.
      * pose proof (fx_nested_step_bounded EX EC L plan mode S
          (NestedState.Make values [] (NestedFrame.Make (NestedVisit x rest) restart :: frames)
            dirty changed)) as Hselected.
        apply fx_machine_events_bound in Hselected.
        unfold fx_nested_step, fx_nested_step_input_budget in *.
        cbn [NestedState.current NestedState.ready NestedState.frames NestedState.dirty
          NestedState.changed NestedFrame.remaining NestedFrame.restart] in *.
        destruct (audit_map_code_get (encode EX x) (NestedPlan.targets plan)) as [raw events].
        cbn [snd app] in Hselected |- *; unfold fx_nested_budget in Hselected;
              cbn [app fold_right fx_nested_event_budget] in Hselected; lia.
      * pose proof (fx_nested_step_bounded EX EC L plan mode S
          (NestedState.Make values [] (NestedFrame.Make (NestedComponent h body rest) restart ::
            frames) dirty changed)) as Hselected.
        apply fx_machine_events_bound in Hselected.
        unfold fx_nested_step, fx_nested_step_input_budget in *.
        cbn [NestedState.current NestedState.ready NestedState.frames NestedState.dirty
          NestedState.changed NestedFrame.remaining NestedFrame.restart] in *.
        destruct (audit_finset_remove (fx_index_encoder EX) h dirty) as [next events].
        cbn [snd app] in Hselected |- *; unfold fx_nested_budget in Hselected;
              cbn [app fold_right fx_nested_event_budget] in Hselected; lia.
  - pose proof (@fx_query_budget X C A EX EC L (System.rhs S c) values) as Hquery.
    pose proof (@fx_query_erases X C A EX L (System.rhs S c) values) as Herase.
    unfold fx_nested_step, fx_nested_step_input_budget.
    cbn [NestedState.current NestedState.ready NestedState.frames NestedState.dirty
      NestedState.changed].
    destruct (fx_model_query EX L (System.rhs S c) values) as [[[value reads] sides] events].
    change (fx_declared_model_work EC events <=
      fx_fullcheck_query_input_budget EX L values (System.rhs S c)) in Hquery.
    change ((value, reads, sides) = Query.run (System.rhs S c) (lookup EX L values)) in Herase.
    rewrite <- Herase.
    pose proof (fx_nested_updates_input_bound ((System.target S c, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as Hupdates.
    destruct (fx_nested_updates EX L plan mode ((System.target S c, value) :: sides)
      (NestedState.Make values rest frames dirty changed)) as [out later].
    cbn [snd] in Hupdates |- *.
    change (1 + (1 + (fx_declared_model_work EC events + (1 + fx_nested_work EC later))) <=
      3 + fx_fullcheck_query_input_budget EX L values (System.rhs S c) +
        fx_nested_updates_input_budget EX L plan mode ((System.target S c, value) :: sides)
          (NestedState.Make values rest frames dirty changed)); lia.
Qed.

Lemma fx_nested_tick_input_bound result :
  fx_nested_work EC (snd (fx_nested_tick EX L plan mode S result)) <=
    fx_nested_tick_input_budget EX L plan mode S result.
Proof.
  destruct result as [state|values]; [|reflexivity].
  pose proof (fx_nested_step_input_bound state) as Hstep.
  unfold fx_nested_tick, fx_nested_tick_input_budget.
  destruct (fx_nested_step EX L plan mode S state) as [next events].
  cbn [snd] in Hstep; destruct next; cbn [snd];
    change (1 + fx_nested_work EC (events ++ [FxNestedCase 14]) <=
      2 + fx_nested_step_input_budget EX L plan mode S state);
    rewrite fx_nested_work_app; change (1 + (fx_nested_work EC events + 1) <=
      2 + fx_nested_step_input_budget EX L plan mode S state); lia.
Qed.

Lemma fx_nested_loop_input_bound_aux fuel state :
  fx_nested_work EC (snd (fx_nested_loop EX L plan mode S fuel state)) <=
    fx_nested_loop_input_budget EX L plan mode S fuel state.
Proof.
  revert state; induction fuel as [fuel IH|fuel IH|]; intro state.
  - pose proof (IH state) as Hfirst.
    pose proof (fx_nested_loop_erases EX L plan mode S fuel state) as Herase.
    cbn [fx_nested_loop fx_nested_loop_input_budget].
    destruct (fx_nested_loop EX L plan mode S fuel state) as [first events] eqn:Hrun.
    cbn [snd] in Hfirst; change (first = nested_loop (nested_step EX L plan mode S) fuel state)
      in Herase; rewrite <- Herase.
    destruct first as [next|values].
    + pose proof (IH next) as Hsecond.
      pose proof (fx_nested_loop_erases EX L plan mode S fuel next) as Herase2.
      destruct (fx_nested_loop EX L plan mode S fuel next) as [second later] eqn:Hnext.
      cbn [snd] in Hsecond; change (second = nested_loop (nested_step EX L plan mode S) fuel next)
        in Herase2; rewrite <- Herase2.
      pose proof (fx_nested_tick_input_bound second) as Htick.
      destruct (fx_nested_tick EX L plan mode S second) as [out last]; cbn [snd] in Htick |- *.
      change (1 + fx_nested_work EC (events ++ (FxNestedCase 16 :: later) ++ last) <=
        2 + fx_nested_loop_input_budget EX L plan mode S fuel state +
        fx_nested_loop_input_budget EX L plan mode S fuel next +
        fx_nested_tick_input_budget EX L plan mode S second).
      repeat rewrite fx_nested_work_app.
      change (1 + (fx_nested_work EC events + ((1 + fx_nested_work EC later) +
        fx_nested_work EC last)) <=
        2 + fx_nested_loop_input_budget EX L plan mode S fuel state +
        fx_nested_loop_input_budget EX L plan mode S fuel next +
        fx_nested_tick_input_budget EX L plan mode S second); lia.
    + pose proof (fx_nested_tick_input_bound (inr values)) as Htick.
      destruct (fx_nested_tick EX L plan mode S (inr values)) as [out last]; cbn [snd] in Htick |-
        *.
      change (1 + fx_nested_work EC (events ++ [FxNestedCase 16] ++ last) <=
        2 + fx_nested_loop_input_budget EX L plan mode S fuel state + 0 +
        fx_nested_tick_input_budget EX L plan mode S (inr values)).
      repeat rewrite fx_nested_work_app; cbn [fx_nested_tick_input_budget] in Htick |- *.
      change (1 + (fx_nested_work EC events + ((1 + 0) + fx_nested_work EC last)) <=
        2 + fx_nested_loop_input_budget EX L plan mode S fuel state + 0 + 1); lia.
  - pose proof (IH state) as Hfirst.
    pose proof (fx_nested_loop_erases EX L plan mode S fuel state) as Herase.
    cbn [fx_nested_loop fx_nested_loop_input_budget].
    destruct (fx_nested_loop EX L plan mode S fuel state) as [first events].
    cbn [snd] in Hfirst; change (first = nested_loop (nested_step EX L plan mode S) fuel state)
      in Herase; rewrite <- Herase.
    destruct first as [next|values].
    + pose proof (IH next) as Hsecond.
      destruct (fx_nested_loop EX L plan mode S fuel next) as [out later]; cbn [snd] in Hsecond |-
        *.
      change (1 + fx_nested_work EC (events ++ FxNestedCase 16 :: later) <=
        2 + fx_nested_loop_input_budget EX L plan mode S fuel state +
        fx_nested_loop_input_budget EX L plan mode S fuel next).
      rewrite fx_nested_work_app.
      change (1 + (fx_nested_work EC events + (1 + fx_nested_work EC later)) <=
        2 + fx_nested_loop_input_budget EX L plan mode S fuel state +
        fx_nested_loop_input_budget EX L plan mode S fuel next); lia.
    + cbn [snd].
      change (1 + fx_nested_work EC (events ++ [FxNestedCase 16]) <=
        2 + fx_nested_loop_input_budget EX L plan mode S fuel state + 0).
      rewrite fx_nested_work_app.
      change (1 + (fx_nested_work EC events + 1) <=
        2 + fx_nested_loop_input_budget EX L plan mode S fuel state + 0); lia.
  - pose proof (fx_nested_tick_input_bound (inl state)) as Htick.
    cbn [fx_nested_loop fx_nested_loop_input_budget].
    destruct (fx_nested_tick EX L plan mode S (inl state)) as [out events]; cbn [snd] in Htick |- *.
    change (1 + fx_nested_work EC events <= 1 + fx_nested_tick_input_budget EX L plan mode S
      (inl state)); lia.
Qed.

End MachineInput.

(** The loop cost is bounded by the recurrence over its original fuel and native states. *)
Theorem fx_nested_loop_input_bound : fx_nested_loop_input_bound_statement.
Proof.
  intros X C A EX EC L plan mode S fuel state.
  pose proof (fx_nested_loop_erases EX L plan mode S fuel state) as Herase.
  pose proof (fx_nested_loop_input_bound_aux EX EC L plan mode S fuel state) as Hbound.
  destruct (fx_nested_loop EX L plan mode S fuel state) as [out events].
  cbn [fst snd] in Herase, Hbound |- *; auto.
Qed.
