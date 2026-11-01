(** * Narrowing callback source receipts

    The same narrowing run retains each external callback occurrence and its operand.
    For example, a rejected narrowing test emits no narrowing callback body.
    Builds on: FixpointAuditNarrow and FixpointAuditWorklistCallbacks. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointNarrow.
From Galois.Collections Require Import CollectionsAuditCost CollectionsAuditFinSet.
From Galois.Fixpoint Require Import FixpointAuditWorklist FixpointAuditWorklistBudget
  FixpointAuditWorklistCallbacks FixpointAuditCheckCallbacks FixpointAuditNarrowCheck
    FixpointAuditNarrowDiscovery
  FixpointAuditNarrow.
Import List.ListNotations.

Record fx_narrow_extra_source (X C A B : Type) := FxNarrowExtraSource {
  fx_narrow_sides_source : C -> list X -> list B -> Prop;
  fx_narrow_operation_source : A -> A -> A -> list B -> Prop
}.

Arguments fx_narrow_sides_source {X C A B} _ _ _ _.

Arguments fx_narrow_operation_source {X C A B} _ _ _ _ _.

Record fx_narrow_extra_budget (X C A B : Type) := FxNarrowExtraBudget {
  fx_narrow_sides_bound : C -> nat;
  fx_narrow_operation_bound : A -> A -> nat
}.

Arguments fx_narrow_sides_bound {X C A B} _ _.

Arguments fx_narrow_operation_bound {X C A B} _ _ _.

Definition fx_narrow_entries {X}
    (events : list (audit_set_event X (fx_encoder_entry X))) : list (fx_encoder_entry X) :=
  flat_map (fun event =>
    match event with
    | AuditSetAdd _ _ _ _ body _ => body
    | AuditSetMem _ _ _ _ body _ => body
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

(** The supplied encoder body satisfies the declared unknown-key source relation for its key and
    code. *)
Definition fx_narrow_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry X) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry x code => fx_source_encode_x source x code body
  end.

(** Target, side and distinct-set dependency events relate their bodies to their sources; other
    dependency events require no bodies. *)
Definition fx_narrow_dep_source {X C A B} (source : fx_declared_callback_source X C A B)
    (extra : fx_narrow_extra_source X C A B) (event : fx_dependency_event X C)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxDepTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxDepSides c out => exists body, bodies = [body] /\ fx_narrow_sides_source extra c out body
  | FxDepDistinct _ _ _ events _ =>
      Forall2 (fx_narrow_entry_source source) (fx_narrow_entries events) bodies
  | _ => bodies = []
  end.

(** Dependency, query, checker, RHS, target, lattice and encoder events relate their bodies to
    their sources; other narrowing events require no bodies. *)
Definition fx_narrow_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (extra : fx_narrow_extra_source X C A B) (event : fx_narrow_event X C A)
    (bodies : list (list B)) : Prop :=
  match event with
  | FnarrowDep events => exists groups,
      Forall2 (fx_narrow_dep_source source extra) events groups /\ bodies = concat groups
  | FnarrowQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FnarrowCheck events => exists groups,
      Forall2 (fx_narrow_check_source source) events groups /\ bodies = concat groups
  | FnarrowRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FnarrowTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FnarrowJoin a b out => exists body, bodies = [body] /\ fx_source_join source a b out body
  | FnarrowLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | FnarrowNarrow a b out => exists body,
      bodies = [body] /\ fx_narrow_operation_source extra a b out body
  | FnarrowIndexGet x code _ _ _
  | FnarrowSet x _ code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | _ => bodies = []
  end.

(** Narrowing events and their callback-body groups correspond in order. *)
Definition fx_narrow_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (extra : fx_narrow_extra_source X C A B) (events : list (fx_narrow_event X C A))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_narrow_event_source source extra) events bodies.

Definition fx_narrow_entries_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entries : list (fx_encoder_entry X)) : nat :=
  fold_right (fun entry total =>
    match entry with
    | FxEncodeEntry x _ => fx_budget_encode_x budget x + total
    end) 0 entries.

Definition fx_narrow_dep_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (extra : fx_narrow_extra_budget X C A B) (event : fx_dependency_event X C) : nat :=
  match event with
  | FxDepTarget c _ => fx_budget_target budget c
  | FxDepSides c _ => fx_narrow_sides_bound extra c
  | FxDepDistinct _ _ _ events _ => fx_narrow_entries_budget budget (fx_narrow_entries events)
  | _ => 0
  end.

Definition fx_narrow_event_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (extra : fx_narrow_extra_budget X C A B)
    (event : fx_narrow_event X C A) : nat :=
  match event with
  | FnarrowDep events => fold_right (fun e n => fx_narrow_dep_budget budget extra e + n) 0 events
  | FnarrowQuery events => fx_declared_external_trace_budget budget events
  | FnarrowCheck events => fold_right (fun e n => fx_narrow_check_budget budget e + n) 0 events
  | FnarrowRhs c _ => fx_budget_rhs budget c
  | FnarrowTarget c _ => fx_budget_target budget c
  | FnarrowJoin a b _ => fx_budget_join budget a b
  | FnarrowLeb a b _ => fx_budget_leb budget a b
  | FnarrowNarrow a b _ => fx_narrow_operation_bound extra a b
  | FnarrowIndexGet x _ _ _ _
  | FnarrowSet x _ _ _ _ _ => fx_budget_encode_x budget x
  | _ => 0
  end.

Definition fx_narrow_external_trace_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (extra : fx_narrow_extra_budget X C A B)
    (events : list (fx_narrow_event X C A)) : nat :=
  fold_right (fun event n => fx_narrow_event_external_budget budget extra event + n) 0 events.

(** The narrowing-specific callbacks have source witnesses for their concrete operations and
    bounded bodies. *)
Definition fx_narrow_extra_laws {X C A B} (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (source : fx_narrow_extra_source X C A B)
    (budget : fx_narrow_extra_budget X C A B) (weight : B -> nat) : Prop :=
  (forall c, exists body, fx_narrow_sides_source source c (side_targets SS c) body) /\
  (forall a b, exists body, fx_narrow_operation_source source a b (narrow L a b) body) /\
  (forall c out body, fx_narrow_sides_source source c out body ->
    fx_one_body_work weight body <= fx_narrow_sides_bound budget c) /\
  (forall a b out body, fx_narrow_operation_source source a b out body ->
    fx_one_body_work weight body <= fx_narrow_operation_bound budget a b).

(** Encoder, target, right-hand-side, reachable continuation and lattice callbacks have source
    witnesses and bounded bodies. *)

Definition fx_narrow_core_laws {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall k a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
    exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body) /\
  (forall a b, exists body, fx_source_join source a b (join L a b) body) /\
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) /\
  (forall c out body, fx_source_rhs source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_rhs budget c) /\
  (forall k a out body, fx_source_continuation source k a out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_continuation budget k a) /\
  (forall a b out body, fx_source_leb source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_leb budget a b) /\
  (forall a b out body, fx_source_join source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_join budget a b).

(** A checked run has same-invocation callback receipts and an independent phase bound. *)

(** With the core and extra narrowing source laws and their bounds, checked narrowing has its
    original result, source receipts and a work bound. *)
Definition fx_narrow_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A)
    (S : System.t X C A) (SS : System.static S) ix rounds input
    (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B)
    (extra : fx_narrow_extra_source X C A B) (extra_budget : fx_narrow_extra_budget X C A B),
    fx_narrow_core_laws EX L S source budget ->
    fx_narrow_extra_laws L S SS extra extra_budget (fx_body_weight budget) ->
    let '(out, events) := fx_narrow_checked_counted EX L S SS ix rounds input in
    exists bodies, fx_narrow_trace_source source extra events bodies /\
      out = narrow_checked EX L S SS ix rounds input /\
      fx_narrow_work EX EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_narrow_checked_input_budget EX L S SS ix rounds input +
        fx_narrow_external_trace_budget budget extra_budget events.
