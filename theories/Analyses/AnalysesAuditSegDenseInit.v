(** * Dense must-lattice initialization

    Constructing the finite must lattice creates its bottom from the whole expression universe.
    For example, an empty universe produces an empty bottom without any key insertion.
    Builds on: AnalysesAuditSegDenseUniverse and the shared finite-set source model. *)
From Stdlib Require Import List PArith Arith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet CollectionsAuditFinSet.
From Galois.Order Require Import OrderLattice.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Views Require Import ViewsGraph.
From Galois.Analyses Require Import AnalysesAvailable AnalysesAuditSegBuilder
  AnalysesAuditSegUniverse
  AnalysesAuditSegDenseUniverse AnalysesAuditSegDenseTransfer AnalysesAuditSegDenseSystem
  AnalysesAuditSegDenseBudget.
Import List.ListNotations.

(** * Dense must-lattice initialization *)

(** The one initial value captures both its universe and actual set insertions. *)
Definition audit_dense_initial {N E U B} (g : Graph.t N E) (cb : audit_seg_build_callbacks N E
    U B) :
    FinSet.t U * list (audit_dense_fx_event N E U B) :=
  let '(universe, universe_events) := audit_dense_universe g cb in
  let '(out, set_events) := audit_finset_of_list (seg_build_expr_encode cb) universe in
  (out, [DenseFxUniverse universe_events; DenseFxTransfer [DenseTransferSet set_events]]).

(** The initial work is determined by the captured universe and insertion events. *)
Definition audit_dense_initial_work {N E U B} (weight : B -> nat)
    (events : list (audit_dense_fx_event N E U B)) : nat :=
  fold_right (fun e n => audit_dense_fx_event_work weight e + n) 0 events.

(** The input budget uses the real universe, including duplicate-free key widths. *)
Definition audit_dense_initial_budget {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (costs : audit_dense_client_budget N E U) : nat :=
  let universe := expr_universe EU gk in
  audit_dense_universe_budget EU gk + audit_dense_universe_external_budget gk costs + 512 +
    fold_right (fun u n => 16 + 16 * Pos.size_nat (encode EU u) + dense_expr_budget costs u + n)
      0 universe.

(** Under callback laws, the counted set is the must-lattice bottom and obeys its work bound. *)
Definition audit_dense_initial_source_statement : Prop :=
  forall (S O N E U C B : Type) (EU : encoding U) (gk : genkill_view S O N E U C)
    (cb : audit_seg_build_callbacks N E U B) (weight : B -> nat) (costs :
    audit_dense_client_budget N E U)
    out_source gen_source expr_source,
    (forall n, fst (seg_build_out cb n) = Graph.out (cfg (gkview gk)) n) ->
    (forall e, fst (seg_build_gen cb e) = gen gk e) ->
    (forall u, fst (seg_build_expr_encode cb u) = encode EU u) ->
    audit_graph_external_callback_adapter (seg_build_out cb) weight out_source
      (dense_out_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_gen cb) weight gen_source
      (dense_gen_budget costs) ->
    audit_graph_external_callback_adapter (seg_build_expr_encode cb) weight expr_source
      (dense_expr_budget costs) ->
    let '(out, events) := audit_dense_initial (cfg (gkview gk)) cb in
    out = proj1_sig (bot (avail_lattice EU gk)) /\
      audit_dense_initial_work weight events <= audit_dense_initial_budget EU gk costs.
