(** * RewriteAuditProofFacts

    Models fact-strategy execution and factful tracked runs with source work.
    For example, zero fuel returns the input facts without running the strategy.
    Builds on: RewriteAuditIndexPrograms and
    RewriteAuditProofApply. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexPrograms RewriteAuditIndexReference
  RewriteAuditIndexRules RewriteAuditProofApply RewriteAuditProofRebuild RewriteAuditProofRun
  RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_rp_fact_program (K Sort V H F : Type) : Type :=
  | RPFactReturn : option (rw_attempt K Sort V H) -> nat -> rw_rp_fact_program K Sort V H F
  | RPFactView : forall R, nat -> rw_rp_view_request K Sort V R ->
      (R -> rw_rp_fact_program K Sort V H F) -> rw_rp_fact_program K Sort V H F
  | RPFactLookup : nat -> rw_id -> (F -> rw_rp_fact_program K Sort V H F) ->
      rw_rp_fact_program K Sort V H F.
Arguments RPFactReturn {K Sort V H F}.
Arguments RPFactView {K Sort V H F R}.
Arguments RPFactLookup {K Sort V H F}.

Inductive rw_rp_fact_receipt (K Sort V F : Type) : Type :=
  | RPFactSnapshot : rw_rp_query_receipt K Sort V -> rw_rp_fact_receipt K Sort V F
  | RPFactRead : list (audit_map_event rw_id F (audit_basic_encoding_event positive)) ->
      rw_rp_fact_receipt K Sort V F.
Arguments RPFactSnapshot {K Sort V F}.
Arguments RPFactRead {K Sort V F}.

Record rw_rp_fact_strategy_adapter (K Sort V H F : Type) := RwRpFactStrategyAdapter {
  rw_rp_fact_strategy_program : rw_rp_fact_program K Sort V H F
}.
Arguments rw_rp_fact_strategy_program {K Sort V H F}.

Fixpoint rw_rp_fact_execute {K Sort V H F} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (state : rw_index_state K Sort V) (unknown : F)
    (facts : Map.t rw_id F) (program : rw_rp_fact_program K Sort V H F) :
    option (rw_attempt K Sort V H) * nat * list (rw_rp_fact_receipt K Sort V F) :=
  match program with
  | RPFactReturn offer body => (offer, 64 + body, nil)
  | RPFactView body request next =>
    let '(answer, receipt) := rw_rp_view_execute_request op value state request in
    let '(offer, later_work, later) :=
      rw_rp_fact_execute op value state unknown facts (next answer) in
    (offer, 64 + body + rw_rp_query_receipt_work receipt + later_work,
      RPFactSnapshot receipt :: later)
  | RPFactLookup body id next =>
    let '(answer, trace) := audit_map_get audit_positive_encode id facts in
    let observed :=
      match answer with
      | Some fact => fact
      | None => unknown
      end in
    let '(offer, later_work, later) :=
      rw_rp_fact_execute op value state unknown facts (next observed) in
    (offer, 64 + body + audit_map_source_work audit_basic_encoding_work trace + later_work,
      RPFactRead trace :: later)
  end.

Definition rw_rp_fact_strategy_run {K Sort V H F} (op : rw_queue_encoder_adapter K)
    (value : rw_queue_encoder_adapter V) (adapter : rw_rp_fact_strategy_adapter K Sort V H F)
    (state : rw_index_state K Sort V) (unknown : F) (facts : Map.t rw_id F) :=
  rw_rp_fact_execute op value state unknown facts (rw_rp_fact_strategy_program adapter).

Definition rw_rp_fact_run_once {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (unknown : F) (strategy : rw_rp_fact_strategy_adapter K Sort V H F)
    (state : rw_rp_run_state K Sort V H * Map.t rw_id F) :
    (rw_rp_run_state K Sort V H * Map.t rw_id F) * nat :=
  let '(run, facts) := state in
  if rw_rp_stopped run then (state, 64)
  else
    let tracked := rw_rp_current run in
    let '(offer, body_work, receipts) := rw_rp_fact_strategy_run op value strategy
      (rw_tracked_machine tracked) unknown facts in
    let prefix := 64 + body_work in
    match offer with
    | None =>
      ((RwRpRunState tracked true (rw_rp_position run) (rw_rp_events run), facts), prefix)
    | Some attempt =>
      let '(applied, work) :=
        rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table
          (rw_rp_position run) tracked attempt in
      match applied with
      | None =>
        ((RwRpRunState tracked false (S (rw_rp_position run))
          (RWRunRejected attempt :: rw_rp_events run), facts), prefix + work)
      | Some (next, events) =>
        ((RwRpRunState next false (S (rw_rp_position run))
          (RWRunAccepted attempt events :: rw_rp_events run), Map.empty), prefix + work + 64)
      end
    end.

Fixpoint rw_rp_fact_run_repeat {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (unknown : F) (strategy : rw_rp_fact_strategy_adapter K Sort V H F) (fuel : positive)
    (state : rw_rp_run_state K Sort V H * Map.t rw_id F) :
    (rw_rp_run_state K Sort V H * Map.t rw_id F) * nat :=
  if rw_rp_stopped (fst state) then (state, 64)
  else
    match fuel with
    | xH =>
      let '(out, work) := rw_rp_fact_run_once EK ES EV op sort value
        hole callbacks table unknown strategy state in
      (out, 64 + work)
    | xO rest =>
      let '(middle, mw) :=
        rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown strategy rest
          state in
      let '(out, tw) := rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown
        strategy rest middle in
      (out, 64 + mw + tw)
    | xI rest =>
      let '(first, fw) :=
        rw_rp_fact_run_once EK ES EV op sort value hole callbacks table unknown strategy state in
      let '(middle, mw) := rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table
        unknown strategy rest first in
      let '(out, tw) := rw_rp_fact_run_repeat EK ES EV op sort value
        hole callbacks table unknown strategy rest middle in
      (out, 64 + fw + mw + tw)
    end.

Definition rw_rp_fact_run_atomic {K Sort V H F} (EK : encoding K) (ES : encoding Sort)
    (EV : encoding V) (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list (rw_rule K Sort V H))
    (unknown : F) (strategy : rw_rp_fact_strategy_adapter K Sort V H F) (fuel : N)
    (input : rw_tracked_state K Sort V H * Map.t rw_id F) :
    (rw_tracked_output K Sort V H * Map.t rw_id F) * nat :=
  let '(initial, facts) := input in
  match fuel with
  | N0 =>
    ((RwTrackedOutput initial RWFuelExhausted nil nil, facts), 64)
  | Npos p =>
    let '(table, rule_preparation_work) := rw_rp_rule_table_atomic rules 0 in
    let '((ready, initial_events), initial_work) := rw_rp_rebuild_atomic op sort value 0 initial in
    let '((final, retained), run_work) :=
      rw_rp_fact_run_repeat EK ES EV op sort value hole callbacks table unknown strategy p
        (RwRpRunState ready false 0 nil, Map.empty) in
    ((RwTrackedOutput (rw_rp_current final)
      (if rw_rp_stopped final then RWStopped else RWFuelExhausted)
      initial_events (rw_rp_events final), retained),
      128 + initial_work + run_work + rule_preparation_work)
  end.

(** Positive-fuel fact-source runs with the same tracked state produce the same result
    and work regardless of their initial fact stores. *)
Definition rw_rp_fact_initial_invalidation_statement : Prop :=
  forall K Sort V H F (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) rules (unknown : F)
    (adapter : rw_rp_fact_strategy_adapter K Sort V H F) p initial first second,
    rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks rules unknown adapter (Npos p)
      (initial, first) =
      rw_rp_fact_run_atomic EK ES EV op sort value hole callbacks rules unknown adapter (Npos p)
        (initial, second).
