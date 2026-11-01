(** * Rooted full-checker callback receipts

    The checker source model relates only callbacks reached from actual system constraints.
    For example, an unrelated constraint identifier supplies no continuation obligation.
    Builds on: FixpointAuditNarrowCheck and the declared callback source model. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCheck
  FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditNarrowCheck.
Import List.ListNotations.

Definition fx_local_set_entries {K}
    (events : list (audit_set_event K (fx_encoder_entry K))) : list (fx_encoder_entry K) :=
  flat_map (fun event =>
    match event with
    | AuditSetAdd _ _ _ _ body _ => body
    | AuditSetMem _ _ _ _ body _ => body
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

(** An unknown-key encoding receipt uses the source relation for the encoded key and code. *)
Definition fx_local_x_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry X) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry x code => fx_source_encode_x source x code body
  end.

(** A constraint-key encoding receipt uses the source relation for the encoded key and code. *)
Definition fx_local_c_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry C) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry c code => fx_source_encode_c source c code body
  end.

Definition fx_local_x_entries_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entries : list (fx_encoder_entry X)) : nat :=
  fold_right (fun entry n =>
    match entry with
    | FxEncodeEntry x _ => fx_budget_encode_x budget x + n
    end) 0 entries.

Definition fx_local_c_entries_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (entries : list (fx_encoder_entry C)) : nat :=
  fold_right (fun entry n =>
    match entry with
    | FxEncodeEntry c _ => fx_budget_encode_c budget c + n
    end) 0 entries.

(** Query, right-hand-side, target and comparison events relate their callback bodies to their
    sources; other checker events require no bodies. *)
Definition fx_narrow_check_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_fullcheck_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FfcQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FfcRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FfcTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FfcLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | _ => bodies = []
  end.

Definition fx_narrow_check_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (event : fx_fullcheck_event X C A) : nat :=
  match event with
  | FfcQuery events => fx_declared_external_trace_budget budget events
  | FfcRhs c _ => fx_budget_rhs budget c
  | FfcTarget c _ => fx_budget_target budget c
  | FfcLeb a b _ => fx_budget_leb budget a b
  | _ => 0
  end.

(** Actual rooted checker callbacks have source witnesses and respect their supplied bounds. *)
Definition fx_fullcheck_rooted_laws {X C A B} (EX : encoding X) (L : lattice A)
    (S : System.t X C A) (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, In c (System.constraints S) ->
    exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, In c (System.constraints S) ->
    exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall k a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
    exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body) /\
  (forall x out body, fx_source_encode_x source x out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_encode_x budget x) /\
  (forall c out body, fx_source_target source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_target budget c) /\
  (forall c out body, fx_source_rhs source c out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_rhs budget c) /\
  (forall k a out body, fx_source_continuation source k a out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_continuation budget k a) /\
  (forall a b out body, fx_source_leb source a b out body ->
    fx_one_body_work (fx_body_weight budget) body <= fx_budget_leb budget a b).

(** Checker events and supplied body groups correspond in order under the per-event source
    relation. *)
Definition fx_fullcheck_rooted_trace_source {X C A B}
    (source : fx_declared_callback_source X C A B) (events : list (fx_fullcheck_event X C A))
    (bodies : list (list (list B))) : Prop := Forall2 (fx_narrow_check_source source) events bodies.

Definition fx_fullcheck_rooted_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (events : list (fx_fullcheck_event X C A)) : nat
      :=
  fold_right (fun event n => fx_narrow_check_budget budget event + n) 0 events.

(** The full-check source statement relates event-body witnesses to rooted callback sources. *)

(** Under the rooted callback laws, checking returns the original result with source receipts and
    a work bound. *)
Definition fx_fullcheck_rooted_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A) m
    (source : fx_declared_callback_source X C A B) (budget : fx_declared_callback_budget X C A B),
    fx_fullcheck_rooted_laws EX L S source budget ->
    let '(out, events) := fx_fullcheck_counted EX L S m in
    exists bodies, fx_fullcheck_rooted_trace_source source events bodies /\
      out = check_post L S (lookup EX L m) /\
      fx_fullcheck_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_fullcheck_input_budget EX L S m + fx_fullcheck_rooted_external_budget budget events.
