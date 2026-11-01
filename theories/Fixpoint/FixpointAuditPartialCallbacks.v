(** * Rooted partial-checker callback receipts

    The actual explored-set checker uses contributors from a well-formed system index.
    For example, duplicate contributors each retain their own callback invocations.
    Builds on: FixpointAuditLocalPartial and FixpointAuditCheckCallbacks. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointPartial
  FixpointAuditWorklistCallbacks FixpointAuditCheckCallbacks FixpointAuditLocalPartial.
Import List.ListNotations.

(** Query, right-hand-side, target, comparison and encoding events relate their bodies to their
    sources; other partial-check events require no bodies. *)
Definition fx_local_partial_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (event : fx_partial_event X C A) (bodies : list (list B)) : Prop :=
  match event with
  | FxPartialQuery events => exists groups,
      fx_declared_trace_source source events groups /\ bodies = concat groups
  | FxPartialRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FxPartialTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxPartialLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | FxPartialMem _ _ _ events =>
      Forall2 (fx_local_x_entry_source source) (fx_local_set_entries events) bodies
  | FxPartialIndexGet x code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | _ => bodies = []
  end.

Definition fx_local_partial_event_budget {X C A B} (budget : fx_declared_callback_budget X C A B)
    (event : fx_partial_event X C A) : nat :=
  match event with
  | FxPartialQuery events => fx_declared_external_trace_budget budget events
  | FxPartialRhs c _ => fx_budget_rhs budget c
  | FxPartialTarget c _ => fx_budget_target budget c
  | FxPartialLeb a b _ => fx_budget_leb budget a b
  | FxPartialMem _ _ _ events => fx_local_x_entries_budget budget (fx_local_set_entries events)
  | FxPartialIndexGet x _ _ _ _ => fx_budget_encode_x budget x
  | _ => 0
  end.

(** Partial-check events and their callback-body groups correspond in order. *)
Definition fx_partial_rooted_trace_source {X C A B}
    (source : fx_declared_callback_source X C A B) (events : list (fx_partial_event X C A))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_local_partial_event_source source) events bodies.

Definition fx_partial_rooted_external_budget {X C A B}
    (budget : fx_declared_callback_budget X C A B) (events : list (fx_partial_event X C A)) : nat :=
  fold_right (fun event n => fx_local_partial_event_budget budget event + n) 0 events.

(** The partial-check source statement uses index laws and rooted callback source witnesses. *)

(** With index laws and rooted checker source laws and bounds, partial checking has its original
    result, source receipts and a work bound. *)
Definition fx_partial_rooted_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix explored m (source : fx_declared_callback_source X C A B)
    (budget : fx_declared_callback_budget X C A B),
    sys_index_laws EX S SS ix -> fx_fullcheck_rooted_laws EX L S source budget ->
    let '(out, events) := check_partial_counted EX L S ix explored m in
    exists bodies, fx_partial_rooted_trace_source source events bodies /\
      out = check_partial EX L S SS ix explored m /\
      fx_partial_work EC events + fx_declared_body_work (fx_body_weight budget) bodies <=
        fx_partial_input_budget EX L S ix explored m + fx_partial_rooted_external_budget budget
          events.
