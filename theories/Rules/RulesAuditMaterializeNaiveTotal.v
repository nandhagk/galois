(** * Whole naive materialization source execution

    Prepared caches feed the canonical RPO scheduler and the distinct total-solver index build.
    For example, storing a stratum result performs the actual assignment lookup for each target.
    Builds on: concrete materialization callbacks, query provenance and canonical FX total runs. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditTotal
  FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesSolve RulesModel
  RulesAuditMaterializePrelude RulesAuditMaterializeAdapters RulesAuditMaterializeJobs
  RulesAuditMaterializeStratify RulesAuditMaterializeDeltaTotal RulesAuditMaterializeNaiveBodies
  RulesAuditMaterializeSystem RulesAuditMaterializeNaiveCallbacks RulesAuditMaterializeTrace
  RulesAuditMaterializeQueryTrace RulesAuditMaterializeNaiveDimensions
  RulesAuditMaterializeReceipts.
Import List.ListNotations.

(** * Naive source runs *)

(** Facts are indexed by the native tail-first atom fold once per prepared-program invocation. *)
Definition mat_facts_by_pred_source {P} (prog : program P) facts :=
  mat_atom_fold prog facts Map.empty.

(** Store each real lookup result from the final assignment, including absent-key bottom. *)
Definition mat_store_total_values {P} (prog : program P) facts (targets : list P)
    (values : assignment P (relation prog facts)) (db : database P) : mat_run (database P) :=
  mat_foldr (fun p before =>
    found <- mat_get (penc prog) p values;;
    let value :=
      match found with
      | Some a => proj1_sig a
      | None => FinSet.empty
      end in
    mat_set (penc prog) p value before) targets db.

(** The proposed storage erasure compares missing-key behavior with the native lookup. *)
Definition mat_store_total_values_erases_statement : Prop :=
  forall P (prog : program P) facts targets values db,
    fst (mat_store_total_values prog facts targets values db) =
      store_relations prog facts targets
        (lookup (penc prog) (relation_lattice prog facts) values) db.

(** The proposed fact-source erasure compares its result with the native facts_by_pred map. *)
Definition mat_facts_by_pred_source_erases_statement : Prop :=
  forall P (prog : program P) facts,
    fst (mat_facts_by_pred_source prog facts) = facts_by_pred prog facts.

(** The proposed cache erasure compares its sets with the native program/fact sets. *)
Definition mat_setup_cached_erases_statement : Prop :=
  forall P (prog : program P) facts,
    fst (mat_setup_cached prog facts) = (preds prog facts, constants prog facts).

(** Events distinguish local frames, scheduler runs and engine callback traces. *)
Inductive mat_naive_event {P} (prog : program P) (facts : list (ground_atom P)) : Type :=
  | MatNaiveFrame (frame : mat_frame)
  | MatNaiveScheduler (st : mat_level_context P) (lower : database P) (k : nat)
      (ri : Map.t nat (rule P)) (run : fx_rpo_result P (rconstraint P) mat_frame)
  | MatNaiveEngine (st : mat_level_context P) (lower : database P) (k : nat)
      (ri : Map.t nat (rule P))
      (index_events : list (fx_index_nested_event P (rconstraint P) mat_frame))
      (init_events engine_events : audit_trace (fx_declared_call P (rconstraint P)
        (relation prog facts)))
      (init_bodies engine_bodies : list (list (list (mat_naive_body_event P)))).

Arguments MatNaiveFrame {P prog facts} _.
Arguments MatNaiveScheduler {P prog facts} _ _ _ _ _.
Arguments MatNaiveEngine {P prog facts} _ _ _ _ _ _ _ _ _.

Definition mat_naive_event_work {P prog facts} (event : @mat_naive_event P prog facts) : nat :=
  match event with
  | MatNaiveFrame frame => mat_frame_work frame
  | MatNaiveScheduler st _ k ri run =>
      fx_rpo_scheduler_work (mat_index_callback_budget prog st k ri) run
  | MatNaiveEngine st _ k ri index_events init_events engine_events init_bodies engine_bodies =>
      fx_index_adapter_work (mat_index_callback_budget prog st k ri) index_events +
      fx_declared_model_work (rconstraint_encoding (penc prog)) init_events +
      fx_declared_model_work (rconstraint_encoding (penc prog)) engine_events +
      fx_declared_body_work mat_naive_body_weight init_bodies +
      fx_declared_body_work mat_naive_body_weight engine_bodies
  end.

Definition mat_naive_event_frames {P prog facts} (event : @mat_naive_event P prog facts)
    : list mat_frame :=
  match event with
  | MatNaiveFrame frame => [frame]
  | MatNaiveScheduler _ _ _ _ run => mat_rpo_callback_frames run
  | MatNaiveEngine _ _ _ _ index_events _ _ init_bodies engine_bodies =>
      flat_map mat_index_callback_frames index_events ++
      mat_naive_bodies_callback_frames init_bodies ++ mat_naive_bodies_callback_frames engine_bodies
  end.

Definition mat_naive_event_dimension {P prog facts} (event : @mat_naive_event P prog facts)
    : nat :=
  match event with
  | MatNaiveFrame frame => mat_width [frame]
  | MatNaiveScheduler st lower k ri run =>
      1 + mat_db_size lower + mat_index_capture_dimension prog st k ri + mat_rpo_dimension run
  | MatNaiveEngine st lower k ri _ init_events engine_events init_bodies engine_bodies =>
      1 + mat_db_size lower + mat_index_capture_dimension prog st k ri +
      mat_engine_trace_dimension prog facts init_events +
      mat_engine_trace_dimension prog facts engine_events +
      mat_width (mat_naive_bodies_callback_frames init_bodies) +
      mat_width (mat_naive_bodies_callback_frames engine_bodies)
  end.

Definition mat_naive_work {P prog facts} (events : list (@mat_naive_event P prog facts)) : nat :=
  fold_right (fun event n => mat_naive_event_work event + n) 0 events.

Definition mat_naive_operand_max {P prog facts} (events : list (@mat_naive_event P prog facts))
    : nat := fold_right (fun event n => Nat.max (mat_naive_event_dimension event) n) 1 events.

Definition mat_naive_callback_frames {P prog facts} (events : list (@mat_naive_event P prog facts))
    : list mat_frame := flat_map mat_naive_event_frames events.

(** A level run records the scheduler, engine callbacks and stored final assignment. *)
Inductive mat_naive_level_run {P} (prog : program P) facts (st : mat_level_context P)
    (cached : FinSet.t P * FinSet.t positive) (ri : Map.t nat (rule P)) (fi : database P)
    (lower : database P) (k : nat) : database P -> list (@mat_naive_event P prog facts) -> Prop :=
  | MatNaiveLevelRun : forall constraints preparation schedule values index_events init_events
      engine_events init_bodies engine_bodies targets target_events final store_events,
      mat_constraints prog facts st k = (constraints, preparation) ->
      schedule = mat_rpo_source prog facts st lower k ri ->
      fx_total_callbacks_run (penc prog) (rconstraint_encoding (penc prog))
        (relation_lattice prog facts)
        (rpo_scheduler (penc prog) (mat_compiled_system prog facts st lower k)
          (mat_compiled_static prog facts st lower k)) Joining
        (mat_compiled_system prog facts st lower k) (mat_index_callbacks prog st k ri)
        values index_events init_events engine_events ->
      mat_naive_trace_source prog facts st lower k cached ri fi schedule
        None init_events init_bodies None ->
      mat_naive_trace_source prog facts st lower k cached ri fi schedule
        None engine_events engine_bodies None ->
      mat_generated_targets prog facts st k = (targets, target_events) ->
      mat_store_total_values prog facts targets values lower = (final, store_events) ->
      mat_naive_level_run prog facts st cached ri fi lower k final
        (map MatNaiveFrame preparation ++ [MatNaiveScheduler st lower k ri schedule;
          MatNaiveEngine st lower k ri index_events init_events engine_events init_bodies
            engine_bodies] ++ map MatNaiveFrame (target_events ++ store_events)).

(** Level runs compose in order, threading each preceding database into the next. *)
Inductive mat_naive_levels_run {P} (prog : program P) facts (st : mat_level_context P)
    (cached : FinSet.t P * FinSet.t positive) (ri : Map.t nat (rule P)) (fi : database P)
    : nat -> database P -> list (@mat_naive_event P prog facts) -> Prop :=
  | MatNaiveLevelsZero :
      mat_naive_levels_run prog facts st cached ri fi 0 Map.empty [MatNaiveFrame (MatBlock 171)]
  | MatNaiveLevelsNext : forall k lower before final events,
      mat_naive_levels_run prog facts st cached ri fi k lower before ->
      mat_naive_level_run prog facts st cached ri fi lower k final events ->
      mat_naive_levels_run prog facts st cached ri fi (S k) final
        (MatNaiveFrame (MatBlock 172) :: before ++ events).

(** An accepted run records one cache, rule-index and fact-index preparation. *)
Inductive mat_naive_program_run {P} (prog : program P) facts :
    option (database P) -> list (@mat_naive_event P prog facts) -> Prop :=
  | MatNaiveProgramRejected : forall setup,
      mat_stratify prog = (None, setup) ->
      mat_naive_program_run prog facts None (map MatNaiveFrame setup)
  | MatNaiveProgramAccepted : forall st setup cached cached_events ri rule_events fi fact_events
      output events,
      mat_stratify prog = (Some st, setup) ->
      mat_setup_cached prog facts = (cached, cached_events) ->
      mat_rule_index 0 (rules prog) = (ri, rule_events) ->
      mat_facts_by_pred_source prog facts = (fi, fact_events) ->
      mat_naive_levels_run prog facts st cached ri fi (count (mat_native_levels st))
        output events ->
      mat_naive_program_run prog facts (Some output)
        (map MatNaiveFrame (setup ++ cached_events ++ [MatBlock 170] ++ rule_events ++ fact_events)
          ++ events).

(** The proposed realization requires a complete execution for every program. *)
Definition mat_naive_program_realization_statement : Prop :=
  forall P (prog : program P) facts,
    exists output events, mat_naive_program_run prog facts output events.

(** The proposed erasure compares a completed run with the public naive solver result. *)
Definition mat_naive_program_erases_statement : Prop :=
  forall P (prog : program P) facts output events,
    mat_naive_program_run prog facts output events -> output = solve_program prog facts.

(** The proposed source bound uses input loops and actual operands without a width premise. *)
Definition mat_naive_program_source_bound_statement : Prop :=
  forall P (prog : program P) facts output events,
    mat_naive_program_run prog facts output events ->
    mat_naive_work events <= mat_naive_whole_budget prog facts (mat_naive_operand_max events).

(** The proposed receipt condition attaches predicate bodies to calls in the same run. *)
Definition mat_naive_program_callback_receipts_statement : Prop :=
  forall P (prog : program P) facts B (source : mat_predicate_callback_source prog B)
      encode_budget arity_budget output events,
    mat_predicate_callback_receipts_statement prog B source ->
    mat_naive_program_run prog facts output events ->
    exists receipts, mat_external_trace_receipts prog B source encode_budget arity_budget
      (mat_naive_callback_frames events) receipts.

(** The proposed full bound adds callback bodies and their per-input allowances. *)
Definition rules_naive_materialization_full_source_statement : Prop :=
  forall P (prog : program P) facts B (source : mat_predicate_callback_source prog B)
      encode_budget arity_budget,
    mat_predicate_callback_receipts_statement prog B source ->
    mat_predicate_callback_input_bounds_statement prog B source encode_budget arity_budget ->
    exists output events receipts,
      mat_naive_program_run prog facts output events /\ output = solve_program prog facts /\
      mat_external_trace_receipts prog B source encode_budget arity_budget
        (mat_naive_callback_frames events) receipts /\
      mat_naive_work events + mat_external_body_work prog B source receipts <=
        mat_naive_whole_budget prog facts (mat_naive_operand_max events) +
          mat_external_trace_allowance B receipts.

(** The consumer condition requires successful well-formed runs to represent the least model. *)
Definition rules_naive_materialization_consumer_statement : Prop :=
  forall P (prog : program P) facts db events,
    program_wf prog facts -> mat_naive_program_run prog facts (Some db) events ->
    represents (rel_of prog db) (least_model prog facts).
