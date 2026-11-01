(** * Literal generated RHS and ask-all continuation bodies

    Capture witnesses describe the generated finite closure family without function extensionality.
    For example, a cons capture applies the saved continuation to a value followed by later values.
    Builds on: RulesAuditMaterializeNaiveBodies and the native relation and query types. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesJoin RulesSolve
  RulesAuditMaterializePrelude RulesAuditMaterializeAdapters RulesAuditJoinSyntax
  RulesAuditMaterializeNaiveBodies.
Import ListNotations.

(** * Captured generated queries *)

Section GeneratedQueries.
Context {P : Type} (prog : program P) (facts : list (ground_atom P)) (st : mat_level_context P)
  (lower : database P) (k : nat) (cached : FinSet.t P * FinSet.t positive).
Local Notation "'A'" := (relation prog facts).

(** A finish context retains the rule, head predicate and ordered dependencies. *)
Record mat_rule_finish_context : Type := MatRuleFinishContext {
  (** Rule whose head is produced by this finish. *)
  mat_finish_rule : rule P;
  (** Predicate to which the result is restricted. *)
  mat_finish_head : P;
  (** Ordered predicates whose values populate the environment. *)
  mat_finish_dependencies : list P
}.

Definition mat_native_finish (ctx : mat_rule_finish_context) (values : list A) : Query.t P A :=
  Query.Ret (restrict prog facts (mat_finish_head ctx)
    (fire_rule prog facts (mat_finish_rule ctx)
      (stratum_env prog facts (mat_native_levels st) (rel_of prog lower) k
        (fill_values (penc prog) (mat_finish_dependencies ctx) values)))).

Definition mat_rule_finish_source (ctx : mat_rule_finish_context) (values : list A) :
    mat_run (Query.t P A) :=
  reads <- mat_fill_values (penc prog) (mat_finish_dependencies ctx) values;;
  fired <- mat_naive_firing prog cached (mat_finish_rule ctx)
    (mat_generated_env prog facts st (mat_rel prog lower) k reads);;
  clamped <- mat_clamp prog cached (mat_finish_head ctx) fired;;
  mat_return (mat_native_finish ctx values).

(** Each constructor captures a literal closure body from ask_all. *)
Inductive mat_finish_capture : (list A -> Query.t P A) -> Type :=
  | MatFinishBase : forall ctx, mat_finish_capture (mat_native_finish ctx)
  | MatFinishCons : forall f, mat_finish_capture f -> forall value : A,
      mat_finish_capture (fun values => f (value :: values)).

Arguments MatFinishCons {f} _ _.

Fixpoint mat_finish_apply {f} (capture : mat_finish_capture f) (values : list A) :
    mat_run (Query.t P A) :=
  match capture with
  | MatFinishBase ctx => mat_rule_finish_source ctx values
  | MatFinishCons previous value => mat_mark 130 (mat_finish_apply previous (value :: values))
  end.

Definition mat_ask_all_source {f} (capture : mat_finish_capture f) (pending : list P) :
    mat_run (Query.t P A) :=
  mat_mark 131 (
    match pending with
    | [] => mat_finish_apply capture []
    | _ => mat_return (ask_all pending f)
    end).

Fixpoint mat_finish_depth {f} (capture : mat_finish_capture f) : nat :=
  match capture with
  | MatFinishBase _ => 0
  | MatFinishCons previous _ => S (mat_finish_depth previous)
  end.

Fixpoint mat_finish_origin {f} (capture : mat_finish_capture f) : mat_rule_finish_context :=
  match capture with
  | MatFinishBase ctx => ctx
  | MatFinishCons previous _ => mat_finish_origin previous
  end.

(** The captured origin names an indexed rule and its actual generated dependencies. *)
Definition mat_finish_origin_valid (ri : Map.t nat (rule P)) {f} (capture : mat_finish_capture f) :
    Prop :=
  let origin := mat_finish_origin capture in
  (exists i, Map.get nat_encoding i ri = Some (mat_finish_rule origin)) /\
  mat_finish_dependencies origin = fst (mat_dependencies prog st k (mat_finish_rule origin)).

(** A generated continuation retains its indexed origin and the remaining dependency count. *)
Inductive mat_generated_continuation_source (ri : Map.t nat (rule P)) :
    (A -> Query.t P A) -> A -> Query.t P A -> list mat_frame -> Prop :=
  | MatGeneratedContinuation : forall f (capture : mat_finish_capture f) pending value
      output events,
      mat_finish_origin_valid ri capture ->
      (mat_finish_depth capture + S (length pending) =
        length (mat_finish_dependencies (mat_finish_origin capture)))%nat ->
      mat_ask_all_source (MatFinishCons capture value) pending = (output, events) ->
      mat_generated_continuation_source ri
        (fun a => ask_all pending (fun values => f (a :: values)))
        value output events.

Definition mat_rhs_source (ri : Map.t nat (rule P)) (fi : database P) (c : rconstraint P) :
    mat_run (Query.t P A) :=
  mat_mark 132 (
    match c with
    | FromRule i head =>
        found <- mat_get_encoded mat_nat_encoder i ri;;
        match found with
        | None => mat_return (Query.Ret (bot (relation_lattice prog facts)))
        | Some r =>
            dependencies <- mat_dependencies prog st k r;;
            let ctx := MatRuleFinishContext r head dependencies in
            mat_ask_all_source (MatFinishBase ctx) dependencies
        end
    | FromFact p =>
        set <- mat_rel prog fi p;; clamped <- mat_clamp prog cached p set;;
        mat_return (Query.Ret (restrict prog facts p set))
    end).

(** The proposed RHS erasure gives the native stratum query for the same indexes. *)
Definition mat_rhs_source_erases_statement : Prop :=
  forall ri fi c,
    fst (mat_rhs_source ri fi c) =
      stratum_rhs prog facts (mat_native_levels st) (rel_of prog lower) k ri fi c.

(** The proposed finish erasure applies the captured native continuation to the same values. *)
Definition mat_finish_apply_erases_statement : Prop :=
  forall f (capture : mat_finish_capture f) values,
    fst (mat_finish_apply capture values) = f values.

(** A generated continuation is required to return its native function at the recorded input. *)
Definition mat_generated_continuation_erases_statement : Prop :=
  forall ri native value result events,
    mat_generated_continuation_source ri native value result events -> result = native value.

(** A valid origin and matching dependency count are required for a continuation receipt. *)
Definition mat_generated_continuation_total_statement : Prop :=
  forall ri f (capture : mat_finish_capture f) pending value,
    mat_finish_origin_valid ri capture ->
    (mat_finish_depth capture + S (length pending) =
      length (mat_finish_dependencies (mat_finish_origin capture)))%nat ->
    exists output events,
      mat_generated_continuation_source ri
        (fun a => ask_all pending (fun values => f (a :: values)))
        value output events.

End GeneratedQueries.
