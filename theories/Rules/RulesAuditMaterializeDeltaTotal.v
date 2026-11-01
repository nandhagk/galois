(** * Finite total execution, strata composition and whole source bound types

    The run relation records repeated prepared steps and the final empty batch.
    For example, a stopped run records the final empty batch and zero additional rounds.
    Builds on: RulesAuditMaterializeRounds and RulesAuditMaterializeStratify. *)

From Stdlib Require Import List NArith PArith Bool.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesModel RulesDelta RulesAuditMaterializePrelude RulesAuditMaterializeAdapters
  RulesAuditJoinSyntax RulesAuditMaterializePlans RulesAuditMaterializeDifference
  RulesAuditMaterializeJobs RulesAuditMaterializeRounds RulesAuditMaterializeStratify.
Import ListNotations.

(** * Runs and their budgets *)

Section TotalRun.
Context {P : Type} (prog : program P) (facts : list (ground_atom P)) (st : mat_level_context P)
  (k : nat) (lower : database P) (cached : FinSet.t P * FinSet.t positive).

(** A run records each prepared step and stops on its first empty batch. *)
Inductive mat_total_run : delta_state P -> delta_state P -> list mat_frame -> nat -> Prop :=
  | MatTotalStop : forall state events,
      mat_prepared_step prog facts st k (mat_rel prog lower) cached state = (None, events) ->
      mat_total_run state state events 0
  | MatTotalNext : forall state next final first rest rounds,
      mat_prepared_step prog facts st k (mat_rel prog lower) cached state = (Some next, first) ->
      mat_total_run next final rest rounds -> mat_total_run state final (first ++ rest) (S rounds).

End TotalRun.

(** A stratum run includes initialization, cached setup and the subsequent total run. *)
Inductive mat_stratum_run {P} strategy (prog : program P) facts (st : mat_level_context P) k
    (lower : database P) : delta_state P -> list mat_frame -> nat -> Prop :=
  | MatStratumRun : forall initial setup cached prepared final rounds events,
      mat_initial strategy prog facts st k (mat_rel prog lower) = (initial, setup) ->
      mat_setup_cached prog facts = (cached, prepared) ->
      mat_total_run prog facts st k lower cached initial final events rounds ->
      mat_stratum_run strategy prog facts st k lower final (setup ++ prepared ++ events) rounds.

(** Successive levels add their accumulated atoms to the preceding database. *)
Inductive mat_levels_run {P} strategy (prog : program P) facts (st : mat_level_context P) :
    nat -> database P -> list mat_frame -> nat -> Prop :=
  | MatLevelsZero : mat_levels_run strategy prog facts st 0 Map.empty [MatBlock 90] 0
  | MatLevelsNext : forall k lower before n1 state body n2 atoms enumeration final output,
      mat_levels_run strategy prog facts st k lower before n1 ->
      mat_stratum_run strategy prog facts st k lower state body n2 ->
      mat_elements (delta_accumulated state) = (atoms, enumeration) ->
      mat_atom_fold prog atoms lower = (final, output) ->
      mat_levels_run strategy prog facts st (S k) final
        (before ++ body ++ enumeration ++ output ++ [MatBlock 91]) (n1 + n2).

Definition mat_bounded_program {P} strategy (prog : program P) facts fuel :=
  stratification <- mat_stratify prog;;
  match stratification with
  | None => mat_return None
  | Some st => mat_bounded_levels strategy prog facts st fuel (count (mat_native_levels st))
  end.

(** A program run records either rejected stratification or all accepted levels. *)
Inductive mat_program_run {P} strategy (prog : program P) facts :
    option (database P) -> list mat_frame -> nat -> Prop :=
  | MatProgramRejected : forall events,
      mat_stratify prog = (None, events) -> mat_program_run strategy prog facts None events 0
  | MatProgramAccepted : forall st setup output events rounds,
      mat_stratify prog = (Some st, setup) ->
      mat_levels_run strategy prog facts st (count (mat_native_levels st)) output events rounds ->
      mat_program_run strategy prog facts (Some output) (setup ++ events) rounds.

Fixpoint mat_terms_dimension (ts : list term) : nat :=
  match ts with
  | [] => 1
  | TVar v :: rest => (1 + v + mat_terms_dimension rest)%nat
  | TConst c :: rest => (1 + Pos.size_nat c + mat_terms_dimension rest)%nat
  end.

Definition mat_atom_dimension {P} (a : atom P) := mat_terms_dimension (args a).

Definition mat_rule_dimension {P} (r : rule P) :=
  (1 + mat_atom_dimension (head r) +
    fold_right (fun lit n => (mat_atom_dimension (lit_atom lit) + n)%nat) 0%nat (body r))%nat.

Definition mat_input_dimension {P} (prog : program P) (facts : list (ground_atom P)) :=
  (1 + fold_right (fun r n => (mat_rule_dimension r + n)%nat) 0%nat (rules prog) +
    fold_right (fun fact n => (mat_tuple_size (snd fact) + n)%nat) 0%nat facts)%nat.

Definition mat_whole_budget input loop_count operand_width :=
  ((N.to_nat 1000000000000%N) * (S input) * (S loop_count) * Nat.pow (S operand_width) 16)%nat.

(** The proposed realization requires a completed total run from every valid delta state. *)
Definition mat_total_realization_statement : Prop :=
  forall P (prog : program P) facts st k lower cached state,
    delta_valid prog facts state ->
    exists final events rounds,
      mat_total_run prog facts st k lower cached state final events rounds.

(** The proposed erasure compares a prepared-cache run with native delta execution. *)
Definition mat_total_erases_statement : Prop :=
  forall P (prog : program P) facts st k lower state (Hvalid : delta_valid prog facts state)
    final events rounds,
    let cached := fst (mat_setup_cached prog facts) in
    mat_total_run prog facts st k lower cached state final events rounds ->
    final = proj1_sig (delta_execute prog facts (mat_native_levels st) k (rel_of prog lower)
      state Hvalid).

(** The proposed uniqueness fixes result, trace and round count for the same state and cache. *)
Definition mat_total_unique_statement : Prop :=
  forall P (prog : program P) facts st k lower cached state f1 e1 n1 f2 e2 n2,
    mat_total_run prog facts st k lower cached state f1 e1 n1 ->
    mat_total_run prog facts st k lower cached state f2 e2 n2 -> f1 = f2 /\ e1 = e2 /\ n1 = n2.

(** The proposed realization requires a completed run for every stratum. *)
Definition mat_stratum_realization_statement : Prop :=
  forall P strategy (prog : program P) facts st k lower,
    exists final events rounds, mat_stratum_run strategy prog facts st k lower final events rounds.

(** The proposed erasure compares the completed stratum with native delta solving. *)
Definition mat_stratum_erases_statement : Prop :=
  forall P strategy (prog : program P) facts st k lower final events rounds,
    mat_stratum_run strategy prog facts st k lower final events rounds ->
    final = delta_solve_stratum strategy prog facts (mat_native_levels st) k (rel_of prog lower).

(** The proposed realization requires a completed run for each finite sequence of levels. *)
Definition mat_levels_realization_statement : Prop :=
  forall P strategy (prog : program P) facts st n,
    exists db events rounds, mat_levels_run strategy prog facts st n db events rounds.

(** The proposed erasure compares completed levels with native delta level solving. *)
Definition mat_levels_erases_statement : Prop :=
  forall P strategy (prog : program P) facts st n db events rounds,
    mat_levels_run strategy prog facts st n db events rounds ->
    db = delta_solve_levels strategy prog facts (mat_native_levels st) n.

(** The proposed realization requires an accepted or rejected run for every program. *)
Definition mat_program_realization_statement : Prop :=
  forall P strategy (prog : program P) facts,
    exists output events rounds, mat_program_run strategy prog facts output events rounds.

(** The proposed erasure compares a program run with the native delta solver result. *)
Definition mat_program_erases_statement : Prop :=
  forall P strategy (prog : program P) facts output events rounds,
    mat_program_run strategy prog facts output events rounds ->
    output = solve_program_delta strategy prog facts.

(** The proposed uniqueness fixes the output, trace and round count of a program run. *)
Definition mat_program_unique_statement : Prop :=
  forall P strategy (prog : program P) facts o1 e1 n1 o2 e2 n2,
    mat_program_run strategy prog facts o1 e1 n1 ->
    mat_program_run strategy prog facts o2 e2 n2 -> o1 = o2 /\ e1 = e2 /\ n1 = n2.

(** The proposed trace bound uses input size, actual rounds and operand width. *)
Definition mat_program_whole_bound_statement : Prop :=
  forall P strategy (prog : program P) facts output events rounds,
    mat_program_run strategy prog facts output events rounds ->
    (mat_work events <= mat_whole_budget (mat_input_dimension prog facts)
      (rounds + length (rules prog)) (mat_width events))%nat.

(** The proposed bounded erasure compares source and native bounded solver results. *)
Definition mat_bounded_program_erases_statement : Prop :=
  forall P strategy (prog : program P) facts fuel,
    fst (mat_bounded_program strategy prog facts fuel) =
      delta_bounded_program strategy prog facts fuel.

(** The proposed bounded trace bound uses the supplied binary fuel. *)
Definition mat_bounded_program_bound_statement : Prop :=
  forall P strategy (prog : program P) facts fuel,
    let '(_, events) := mat_bounded_program strategy prog facts fuel in
    (mat_work events <= mat_whole_budget (mat_input_dimension prog facts) (Pos.to_nat fuel + 1)
      (mat_width events))%nat.

(** The consumer condition requires a successful well-formed run to represent the least model. *)
Definition mat_materialization_consumer_statement : Prop :=
  forall P strategy (prog : program P) facts output events rounds,
    program_wf prog facts -> mat_program_run strategy prog facts output events rounds ->
    forall db, output = Some db -> represents (rel_of prog db) (least_model prog facts).

(** This carrier is a mathematical input budget, not an executed enumeration. *)
Definition mat_program_loop_budget {P} (prog : program P) facts :=
  ((1 + length (rule_nodes prog)) * (1 + length (delta_support prog facts)))%nat.

(** The proposed bound limits rounds of a valid run by its remaining support. *)
Definition mat_total_rounds_input_bound_statement : Prop :=
  forall P (prog : program P) facts st k lower state final events rounds,
    delta_valid prog facts state ->
    mat_total_run prog facts st k lower (fst (mat_setup_cached prog facts))
      state final events rounds ->
    (rounds <= delta_remaining prog facts state)%nat.

(** The proposed program round bound uses the input-derived loop budget. *)
Definition mat_program_rounds_input_bound_statement : Prop :=
  forall P strategy (prog : program P) facts output events rounds,
    mat_program_run strategy prog facts output events rounds ->
    (rounds <= mat_program_loop_budget prog facts)%nat.

(** The proposed work bound uses input dimensions and the same trace width. *)
Definition mat_program_input_loop_bound_statement : Prop :=
  forall P strategy (prog : program P) facts output events rounds,
    mat_program_run strategy prog facts output events rounds ->
    (mat_work events <= mat_whole_budget (mat_input_dimension prog facts)
      (mat_program_loop_budget prog facts) (mat_width events))%nat.

(** The public cost boundary uses the input-derived loop bound. *)
Definition rules_materialization_cost_statement := mat_program_input_loop_bound_statement.

(** The public correspondence boundary uses the program erasure relation. *)
Definition rules_materialization_source_correspondence_statement := mat_program_erases_statement.

(** The public consumer boundary uses the least-model representation condition. *)
Definition rules_materialization_consumer_statement := mat_materialization_consumer_statement.

(** The permitted maximum is measured on this same execution, independently of work. *)
Definition rules_materialization_same_execution_bound_statement :=
  mat_program_input_loop_bound_statement.

(** Client body judgments retain actual encoder and arity inputs, outputs and frames. *)
Record mat_predicate_callback_source {P} (prog : program P) (B : Type) : Type :=
  MatPredicateCallbackSource {
    (** The encoder body relates its predicate, code and sequence of frames. *)
    mat_predicate_encoder_body : P -> positive -> list B -> Prop;
    (** The arity body relates its predicate, result and sequence of frames. *)
    mat_predicate_arity_body : P -> nat -> list B -> Prop;
    (** Frame weights count the supplied predicate callback body work. *)
    mat_predicate_body_frame_weight : B -> nat
  }.

(** The receipt condition requires actual encoder and arity results and positive frame weights. *)
Definition mat_predicate_callback_receipts_statement {P} (prog : program P) B
    (source : mat_predicate_callback_source prog B) : Prop :=
  (forall frame, (1 <= mat_predicate_body_frame_weight _ _ source frame)%nat) /\
  (forall p, exists body, mat_predicate_encoder_body _ _ source p (encode (penc prog) p) body) /\
  (forall p, exists body, mat_predicate_arity_body _ _ source p (arity prog p) body) /\
  (forall p code body, mat_predicate_encoder_body _ _ source p code body ->
    code = encode (penc prog) p) /\
  (forall p value body, mat_predicate_arity_body _ _ source p value body -> value = arity prog p).

(** Each supplied encoder or arity body must fit its own input-dependent allowance. *)
Definition mat_predicate_callback_input_bounds_statement {P} (prog : program P) B
    (source : mat_predicate_callback_source prog B) (encode_budget arity_budget : P -> nat) :
    Prop :=
  (forall p code body, mat_predicate_encoder_body _ _ source p code body ->
    (1 + fold_right (fun frame n => mat_predicate_body_frame_weight _ _ source frame + n) 0 body <=
      encode_budget p)%nat) /\
  (forall p value body, mat_predicate_arity_body _ _ source p value body ->
    (1 + fold_right (fun frame n => mat_predicate_body_frame_weight _ _ source frame + n) 0 body <=
      arity_budget p)%nat).

(** External stratifications supply level functions; captured maps use their own branch. *)
Record mat_external_level_source {P} (st : stratification P) (B : Type) : Type :=
  MatExternalLevelSource {
    (** The level body relates a predicate and returned level to its frames. *)
    mat_external_level_body : P -> nat -> list B -> Prop;
    (** Frame weights count the supplied external level body work. *)
    mat_external_level_frame_weight : B -> nat
  }.

(** External level receipts must return the supplied level within their per-input allowance. *)
Definition mat_external_level_receipts_statement {P} (st : stratification P) B
    (source : mat_external_level_source st B) (input_budget : P -> nat) : Prop :=
  (forall frame, (1 <= mat_external_level_frame_weight _ _ source frame)%nat) /\
  (forall p, exists body, mat_external_level_body _ _ source p (level st p) body) /\
  (forall p value body, mat_external_level_body _ _ source p value body -> value = level st p /\
    (1 + fold_right (fun frame n => mat_external_level_frame_weight _ _ source frame + n) 0 body <=
      input_budget p)%nat).
