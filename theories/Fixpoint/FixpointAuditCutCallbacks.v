(** * FixpointAuditCutCallbacks model

    Cut source receipts: exact same-run external callback and set-encoder bodies.
    For example, a cut set operation retains its encoder body.
    Builds on: FixpointAuditCut and the counted collection models. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointIndex FixpointCut
  FixpointAuditIndex FixpointAuditWorklist FixpointAuditWorklistCallbacks FixpointAuditCut.
Import List.ListNotations.

Definition fx_cut_set_entries {X} (events : list (audit_set_event X (fx_encoder_entry X))) : list
  (fx_encoder_entry X) :=
  flat_map (fun event =>
    match event with
    | AuditSetAdd _ _ _ _ body _
    | AuditSetMem _ _ _ _ body _
    | AuditSetRemove _ _ _ _ body _ => body
    | AuditSetFold _ _ => []
    end) events.

(** The supplied cut-set encoder body satisfies the unknown-key source relation for its key and
    code. *)
Definition fx_cut_entry_source {X C A B} (source : fx_declared_callback_source X C A B)
    (entry : fx_encoder_entry X) (body : list B) : Prop :=
  match entry with
  | FxEncodeEntry x code => fx_source_encode_x source x code body
  end.

(** Set, map, index, query, RHS, target, side, equality and lattice callback events relate their
    bodies to the appropriate sources; other cut events require no bodies. *)
Definition fx_cut_event_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (event : fx_cut_event X C A)
    (bodies : list (list B)) : Prop :=
  match event with
  | FxCutSetMem _ _ _ events
  | FxCutSetAdd _ _ _ events =>
      Forall2 (fx_cut_entry_source source) (fx_cut_set_entries events) bodies
  | FxCutMapGet x code _ _ _
  | FxCutMapSet x _ code _ _ _
  | FxCutIndexGet x code _ _ _ =>
      exists body, bodies = [body] /\ fx_source_encode_x source x code body
  | FxCutQuery events => exists groups, fx_declared_trace_source source events groups /\ bodies =
    concat groups
  | FxCutRhs c out => exists body, bodies = [body] /\ fx_source_rhs source c out body
  | FxCutTarget c out => exists body, bodies = [body] /\ fx_source_target source c out body
  | FxCutSides c out => exists body, bodies = [body] /\ fxi_sides_source index_source c out body
  | FxCutEqual x y cx cy _ _ => exists first second, bodies = [first; second] /\
      fx_source_encode_x source x cx first /\ fx_source_encode_x source y cy second
  | FxCutJoin a b out => exists body, bodies = [body] /\ fx_source_join source a b out body
  | FxCutLeb a b out => exists body, bodies = [body] /\ fx_source_leb source a b out body
  | _ => bodies = []
  end.

(** Cut events and their callback-body groups correspond in order, one group per event. *)
Definition fx_cut_trace_source {X C A B} (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (events : list (fx_cut_event X C A))
    (bodies : list (list (list B))) : Prop :=
  Forall2 (fx_cut_event_source source index_source) events bodies.

(** The supplied source relations admit bodies for the specified encoding, reachable
    continuation, lattice and static-system results. *)
Definition fx_cut_source_laws {X C A B} (EX : encoding X) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) : Prop :=
  (forall x, exists body, fx_source_encode_x source x (encode EX x) body) /\
  (forall c, exists body, fx_source_rhs source c (System.rhs S c) body) /\
  (forall c, exists body, fx_source_target source c (System.target S c) body) /\
  (forall c, exists body, fxi_sides_source index_source c (side_targets SS c) body) /\
  (forall (k : A -> Query.t X A) a, (exists x, fx_declared_query_reachable S (Query.Ask x k)) ->
    exists body, fx_source_continuation source k a (k a) body) /\
  (forall a b, exists body, fx_source_join source a b (join L a b) body) /\
  (forall a b, exists body, fx_source_leb source a b (leb L a b) body).

(** Every accepted side-target callback body fits the bound for its constraint. *)
Definition fx_cut_sides_bounded {X C B} (source : fx_index_external_source X C B)
    (ib : fx_index_external_budget X C B) (weight : B -> nat) : Prop :=
  forall c out body, fxi_sides_source source c out body ->
    fx_one_body_work weight body <= fxi_sides_bound ib c.

Definition fx_cut_event_external_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (event : fx_cut_event X C A) : nat :=
  match event with
  | FxCutSetMem _ _ _ events
  | FxCutSetAdd _ _ _ events =>
      fold_right (fun entry n =>
        match entry with
        | FxEncodeEntry x _ => fx_budget_encode_x wb x + n
        end)
        0 (fx_cut_set_entries events)
  | FxCutMapGet x _ _ _ _
  | FxCutMapSet x _ _ _ _ _
  | FxCutIndexGet x _ _ _ _ => fx_budget_encode_x
    wb x
  | FxCutQuery events => fx_declared_external_trace_budget wb events
  | FxCutRhs c _ => fx_budget_rhs wb c
  | FxCutTarget c _ => fx_budget_target wb c
  | FxCutSides c _ => fxi_sides_bound ib c
  | FxCutEqual x y _ _ _ _ => fx_budget_encode_x wb x + fx_budget_encode_x wb y
  | FxCutJoin a b _ => fx_budget_join wb a b
  | FxCutLeb a b _ => fx_budget_leb wb a b
  | _ => 0
  end.

Definition fx_cut_external_trace_budget {X C A B} (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B) (events : list (fx_cut_event X C A)) : nat :=
  fold_right (fun event n => fx_cut_event_external_budget wb ib event + n) 0 events.

(** With index laws, cut source laws and declared and side callback bounds, expansion has its
    original result, source receipts and a work bound. *)
Definition fx_cut_external_source_statement : Prop :=
  forall X C A B (EX : encoding X) (EC : encoding C) (L : lattice A) (S : System.t X C A)
    (SS : System.static S) ix cert (source : fx_declared_callback_source X C A B)
    (index_source : fx_index_external_source X C B) (wb : fx_declared_callback_budget X C A B)
    (ib : fx_index_external_budget X C B),
    sys_index_laws EX S SS ix ->
    fx_cut_source_laws EX L S SS source index_source -> fx_declared_callback_bounded source wb ->
    fx_cut_sides_bounded index_source ib (fx_body_weight wb) ->
    let '(out, events) := fx_cut_expand_counted EX L S SS ix cert in
    exists bodies, fx_cut_trace_source source index_source events bodies /\
      out = expand EX L S SS ix cert /\
      fx_cut_work EC events + fx_declared_body_work (fx_body_weight wb) bodies <=
        fx_cut_expand_input_budget EX L S SS ix cert + fx_cut_external_trace_budget wb ib events.
