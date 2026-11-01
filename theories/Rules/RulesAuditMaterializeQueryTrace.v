(** * Provenance of generated ask-all continuation calls

    A cursor starts at the actual indexed RHS and advances with that execution's read values.
    For example, a continuation cannot borrow the body of another extensionally equal closure.
    Builds on: RulesAuditMaterializeNaiveQuery and the canonical FX callback trace. *)

From Stdlib Require Import List Bool PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Fixpoint Require Import FixpointQuery FixpointAuditWorklist
  FixpointAuditWorklistCallbacks FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesSolve
  RulesAuditMaterializePrelude RulesAuditMaterializeNaiveBodies RulesAuditMaterializeNaiveQuery
  RulesAuditMaterializeNaiveCallbacks.
Import List.ListNotations.

(** * Continuation provenance *)

Section QueryProvenance.
Context {P : Type} (prog : program P) (facts : list (ground_atom P))
  (st : mat_level_context P) (lower : database P) (k : nat)
  (cached : FinSet.t P * FinSet.t positive) (ri : Map.t nat (rule P)) (fi : database P)
  (schedule : fx_rpo_result P (rconstraint P) mat_frame).
Local Notation "'A'" := (relation prog facts).

(** Only the generated base and cons captures inhabit this cursor. *)
Inductive mat_query_cursor : Type :=
  | MatQueryCursor : forall f,
      mat_finish_capture prog facts st lower k f -> list P -> mat_query_cursor.

Definition mat_cursor_start (c : rconstraint P) : option mat_query_cursor :=
  match c with
  | FromFact _ => None
  | FromRule i head =>
      match fst (mat_get_encoded mat_nat_encoder i ri) with
      | None => None
      | Some r =>
          let dependencies := fst (mat_dependencies prog st k r) in
          let origin := MatRuleFinishContext r head dependencies in
          match dependencies with
          | [] => None
          | _ :: _ =>
              Some (MatQueryCursor _ (MatFinishBase prog facts st lower k origin) dependencies)
          end
      end
  end.

Definition mat_cursor_next {f} (capture : mat_finish_capture prog facts st lower k f)
    (value : A) (pending : list P) : option mat_query_cursor :=
  match pending with
  | [] => None
  | _ :: _ => Some (MatQueryCursor _ (MatFinishCons prog facts st lower k _ capture value) pending)
  end.

Definition mat_event_changes_cursor
    (event : audit_event (fx_declared_call P (rconstraint P) A)) : bool :=
  match event with
  | AuditCall (FxRhs _ _) | AuditCall (FxContinuation _ _ _ _) => true
  | _ => false
  end.

(** A receipt sequence follows the same RHS identity and exact successive captured values. *)
Inductive mat_naive_trace_source : option mat_query_cursor ->
    audit_trace (fx_declared_call P (rconstraint P) A) ->
    list (list (list (mat_naive_body_event P))) -> option mat_query_cursor -> Prop :=
  | MatNaiveTraceNil : forall cursor, mat_naive_trace_source cursor [] [] cursor
  | MatNaiveTraceOther : forall cursor event body rest bodies final,
      mat_event_changes_cursor event = false ->
      fx_declared_event_source
        (mat_naive_declared_source prog facts st lower k cached ri fi schedule) event body ->
      mat_naive_trace_source cursor rest bodies final ->
      mat_naive_trace_source cursor (event :: rest) (body :: bodies) final
  | MatNaiveTraceRhs : forall c q body rest bodies final,
      fx_declared_event_source
        (mat_naive_declared_source prog facts st lower k cached ri fi schedule)
        (AuditCall (FxRhs c q)) body ->
      mat_naive_trace_source (mat_cursor_start c) rest bodies final ->
      mat_naive_trace_source None (AuditCall (FxRhs c q) :: rest) (body :: bodies) final
  | MatNaiveTraceContinuation : forall f
      (capture : mat_finish_capture prog facts st lower k f) x pending value native output
      local rest bodies final,
      native = (fun a => ask_all pending (fun values => f (a :: values))) ->
      mat_ask_all_source prog facts st lower k cached
        (MatFinishCons prog facts st lower k _ capture value) pending = (output, local) ->
      fx_declared_event_source
        (mat_naive_declared_source prog facts st lower k cached ri fi schedule)
        (AuditCall (FxContinuation x value native output)) [map MatNaiveLocal local] ->
      mat_naive_trace_source (mat_cursor_next capture value pending) rest bodies final ->
      mat_naive_trace_source (Some (MatQueryCursor _ capture (x :: pending)))
        (AuditCall (FxContinuation x value native output) :: rest)
        ([map MatNaiveLocal local] :: bodies) final.

(** The proposed forgetting condition maps provenance receipts to ordinary FX trace receipts. *)
Definition mat_naive_trace_source_forgets_statement : Prop :=
  forall initial events bodies final,
    mat_naive_trace_source initial events bodies final ->
    fx_declared_trace_source
      (mat_naive_declared_source prog facts st lower k cached ri fi schedule) events bodies.

End QueryProvenance.
