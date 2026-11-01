(** * Concrete compiled-system callback instances

    The naive solver supplies fixed bodies to the canonical Fixpoint scheduler owner.
    For example, a missing rule index produces an empty static dependency list.
    Builds on: RulesAuditMaterializeNaiveBodies and FixpointAuditScheduleWrapper. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditElements.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointWorklist FixpointSchedule
  FixpointAuditIndex FixpointAuditSchedule FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesSolve
  RulesAuditMaterializePrelude RulesAuditMaterializeNaiveBodies.
Import List.ListNotations.

(** * Generated system callbacks *)

Section GeneratedSystem.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : mat_level_context P) (lower : database P) (k : nat) (ri : Map.t nat (rule P)).

(** This alias selects the native stratum constraint system for the captured inputs. *)
Definition mat_compiled_system :=
  stratum_system prog facts (mat_native_levels st) (rel_of prog lower) k.

(** This alias selects the native static stratum system for the captured inputs. *)
Definition mat_compiled_static :=
  stratum_static prog facts (mat_native_levels st) (rel_of prog lower) k.

Definition mat_target_source (c : rconstraint P) : mat_run P :=
  mat_return (
    match c with
    | FromRule _ h => h
    | FromFact p => p
    end).

(** Generated dependencies and encoders use their concrete bodies at each occurrence. *)
Definition mat_index_callbacks : fx_index_external_model P (rconstraint P) mat_frame :=
  FxIndexExternalModel P (rconstraint P) mat_frame (mat_encode (penc prog))
    mat_target_source (fun _ => mat_return []) (mat_generated_deps prog st k ri).

(** Each source clause records the actual typed callback result and literal body. *)
Definition mat_naive_index_source : fx_index_external_source P (rconstraint P) mat_frame :=
  {|
    (** Encoding receipts record the predicate encoder result and frames. *)
    fxi_encode_source := fun p result body => mat_encode (penc prog) p = (result, body);
    (** Target receipts record the generated target result and frames. *)
    fxi_target_source := fun c result body => mat_target_source c = (result, body);
    (** Side-target receipts record the empty generated side list. *)
    fxi_sides_source := fun _ result body => mat_return [] = (result, body);
    (** Dependency receipts record the indexed rule lookup and generated dependencies. *)
    fxi_deps_source := fun c result body => mat_generated_deps prog st k ri c = (result, body) |}.

(** The proposed callback erasure assumes the captured rule index is the native index. *)
Definition mat_index_callbacks_erases_statement : Prop :=
  ri = index_rules_from 0 (rules prog) ->
  fx_index_external_erases (penc prog) mat_compiled_system mat_compiled_static mat_index_callbacks.

(** Literal callback source equations require no assumed whole-graph or whole-solver law. *)
Definition mat_index_callbacks_source_statement : Prop :=
  fx_dep_source_laws mat_index_callbacks mat_naive_index_source.

End GeneratedSystem.

Definition mat_level_capture_dimension {P} (st : mat_level_context P) : nat :=
  match st with
  | MatExternalLevels _ => 1
  | MatCapturedLevels _ levels bound =>
      1 + bound + audit_trie_nodes levels +
      fold_right (fun entry n => snd entry + n) 0 (Map.elements levels)
  end.

Definition mat_dependency_rule_dimension {P} (prog : program P) st k (r : rule P) : nat :=
  1 + length (body r) + fold_right (fun lit n =>
    let a := lit_atom lit in
    1 + Pos.size_nat (encode (penc prog) (pred a)) +
      level (mat_native_levels st) (pred a) + k + n) 0 (body r).

Definition mat_index_capture_dimension {P} (prog : program P) st k
    (ri : Map.t nat (rule P)) : nat :=
  1 + mat_level_capture_dimension st + audit_trie_nodes ri +
    fold_right (fun entry n =>
      fst entry + mat_dependency_rule_dimension prog st k (snd entry) + n) 0 (Map.elements ri).

(** Per-call bounds use actual callback inputs and captured source data. *)
Definition mat_index_callback_budget {P} (prog : program P) st k (ri : Map.t nat (rule P))
    : fx_index_external_budget P (rconstraint P) mat_frame :=
  {|
    (** Each frame weight includes a positive local contribution. *)
    fxi_body_weight := fun frame => S (mat_frame_work frame);
    (** The encoder callback budget is charged separately. *)
    fxi_encode_bound := fun _ => 2;
    (** The target callback budget covers its fixed local body. *)
    fxi_target_bound := fun _ => 101;
    (** The side-target callback budget covers the fixed empty result. *)
    fxi_sides_bound := fun _ => 101;
    (** The dependency callback budget depends on its index and captured source data. *)
    fxi_deps_bound := fun c =>
      let index :=
        match c with
        | FromRule i _ => i
        | FromFact _ => 0
        end in
      (N.to_nat 1000000%N) * Nat.pow (1 + index + mat_index_capture_dimension prog st k ri) 12 |}.

(** Bounds for generated callbacks are library obligations, never assumed solver bounds. *)
Definition mat_index_callback_bounded_statement : Prop :=
  forall P (prog : program P) st k ri,
    fx_index_external_bounded (mat_index_callbacks prog st k ri)
      (mat_index_callback_budget prog st k ri).

(** The source instance invokes the sole production scheduler owner. *)
Definition mat_rpo_source {P} (prog : program P) facts st lower k ri :=
  fx_rpo_scheduler_counted (penc prog) (mat_compiled_system prog facts st lower k)
    (mat_compiled_static prog facts st lower k) (mat_index_callbacks prog st k ri).

(** The proposed scheduler erasure compares native priority and widening observations. *)
Definition mat_rpo_source_erases_statement : Prop :=
  forall P (prog : program P) facts st lower k ri,
    ri = index_rules_from 0 (rules prog) ->
    let result := mat_rpo_source prog facts st lower k ri in
    let native := rpo_scheduler (penc prog) (mat_compiled_system prog facts st lower k)
      (mat_compiled_static prog facts st lower k) in
    forall x,
      fst (audit_rpo_schedule_priority (fx_dep_encoder (mat_index_callbacks prog st k ri))
        (fx_rpo_positions result) x) = priority native x /\
      fst (audit_rpo_schedule_widening (fx_dep_encoder (mat_index_callbacks prog st k ri))
        (fx_rpo_heads result) x) = widening_point native x.
