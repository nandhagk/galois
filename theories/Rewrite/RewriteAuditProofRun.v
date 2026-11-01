(** * RewriteAuditProofRun

    Models tracked runner iterations, their event lists, and the final source output.
    For example, a stopped runner at position 0 with no events remains unchanged at fuel 1.
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
  RewriteAuditIndexRules RewriteAuditProofApply RewriteAuditProofRebuild RewriteAuditProofSeed
  RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Record rw_rp_run_state (K Sort V H : Type) := RwRpRunState {
  rw_rp_current : rw_tracked_state K Sort V H;
  rw_rp_stopped : bool;
  rw_rp_position : nat;
  rw_rp_events : list (rw_run_event K Sort V H)
}.
Arguments RwRpRunState {K Sort V H}.
Arguments rw_rp_current {K Sort V H}.
Arguments rw_rp_stopped {K Sort V H}.
Arguments rw_rp_position {K Sort V H}.
Arguments rw_rp_events {K Sort V H}.

Definition rw_rp_run_once {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (strategy : rw_rp_strategy_adapter K Sort V H) (state : rw_rp_run_state K Sort V H) :
    rw_rp_run_state K Sort V H * nat :=
  if rw_rp_stopped state then (state, 64)
  else
    let tracked := rw_rp_current state in
    let '(offer, body_work, receipts) :=
      rw_rp_strategy_run op value strategy (rw_tracked_machine tracked) in
    let prefix := 64 + body_work in
    match offer with
    | None =>
      (RwRpRunState tracked true (rw_rp_position state) (rw_rp_events state), prefix)
    | Some attempt =>
      let '(applied, work) :=
        rw_rp_apply_prepared_atomic EK ES EV op sort value hole callbacks table
          (rw_rp_position state) tracked attempt in
      match applied with
      | None =>
        (RwRpRunState tracked false (S (rw_rp_position state))
          (RWRunRejected attempt :: rw_rp_events state), prefix + work)
      | Some (next, events) =>
        (RwRpRunState next false (S (rw_rp_position state))
          (RWRunAccepted attempt events :: rw_rp_events state), prefix + work)
      end
    end.

Fixpoint rw_rp_run_repeat {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (table : Map.t nat (rw_rule K Sort V H))
    (strategy : rw_rp_strategy_adapter K Sort V H) (fuel : positive)
    (state : rw_rp_run_state K Sort V H) :
    rw_rp_run_state K Sort V H * nat :=
  if rw_rp_stopped state then (state, 64)
  else
    match fuel with
    | xH =>
      let '(out, work) :=
        rw_rp_run_once EK ES EV op sort value hole callbacks table strategy state in
      (out, 64 + work)
    | xO rest =>
      let '(middle, mw) :=
        rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest state in
      let '(out, tw) :=
        rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest middle in
      (out, 64 + mw + tw)
    | xI rest =>
      let '(first, fw) :=
        rw_rp_run_once EK ES EV op sort value hole callbacks table strategy state in
      let '(middle, mw) :=
        rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest first in
      let '(out, tw) :=
        rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy rest middle in
      (out, 64 + fw + mw + tw)
    end.

Record rw_tracked_output (K Sort V H : Type) := RwTrackedOutput {
  rw_tracked_final : rw_tracked_state K Sort V H;
  rw_tracked_stop : rw_stop;
  rw_tracked_initial : list rw_index_event;
  rw_tracked_events : list (rw_run_event K Sort V H)
}.
Arguments RwTrackedOutput {K Sort V H}.
Arguments rw_tracked_final {K Sort V H}.
Arguments rw_tracked_stop {K Sort V H}.
Arguments rw_tracked_initial {K Sort V H}.
Arguments rw_tracked_events {K Sort V H}.

Definition rw_rp_run_atomic {K Sort V H} (EK : encoding K) (ES : encoding Sort) (EV : encoding V)
    (op : rw_queue_encoder_adapter K) (sort : rw_queue_encoder_adapter Sort)
    (value : rw_queue_encoder_adapter V) (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rules : list (rw_rule K Sort V H))
    (strategy : rw_rp_strategy_adapter K Sort V H) (fuel : N) (seed : rw_term K Sort V) :
    (rw_id * rw_tracked_output K Sort V H) * nat :=
  let '((root, initial), seed_work) := rw_rp_seed_atomic EK ES EV op value seed in
  match fuel with
  | N0 => ((root, RwTrackedOutput initial RWFuelExhausted nil nil), 64 + seed_work)
  | Npos p =>
    let '(table, rule_preparation_work) := rw_rp_rule_table_atomic rules 0 in
    let '((ready, initial_events), initial_work) := rw_rp_rebuild_atomic op sort value 0 initial in
    let '(final, run_work) :=
      rw_rp_run_repeat EK ES EV op sort value hole callbacks table strategy p
        (RwRpRunState ready false 0 nil) in
    ((root, RwTrackedOutput (rw_rp_current final)
      (if rw_rp_stopped final then RWStopped else RWFuelExhausted)
      initial_events (rw_rp_events final)),
      64 + seed_work + initial_work + run_work + rule_preparation_work)
  end.
