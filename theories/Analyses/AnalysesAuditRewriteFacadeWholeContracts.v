(** * AnalysesAuditRewriteFacadeWholeContracts

    Defines facade external-operation envelopes and prospective whole-operation work bounds.
    For example, a guard return performs no further substitution queries.
    Builds on: AnalysesAuditRewriteFacadeOptimizer and
    RewriteAuditIndexExternal. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeCheckedMaterialize
  AnalysesAuditRewriteFacadeDimensions AnalysesAuditRewriteFacadeOptimizer
  AnalysesAuditRewriteFacadePrepare AnalysesAuditRewriteFacadeReference
  AnalysesAuditRewriteFacadeRun.
From Galois.Rewrite Require Import RewriteAuditIndexExternal RewriteAuditIndexReference
  RewriteAuditProofCarrier RewriteAuditProofRun RewriteAuditProofTick RewriteAuditQueueReference.
Import List.ListNotations.

Fixpoint rw_facade_term_ops {K} (value : term K) : list K :=
  match value with
  | TVar _ => nil
  | TApp op children =>
    op :: (fix visit (terms : list (term K)) : list K :=
      match terms with
      | nil => nil
      | term :: rest => rw_facade_term_ops term ++ visit rest
      end) children
  end.

Fixpoint rw_facade_core_ops {K} (value : rw_term K unit nat) : list K :=
  match value with
  | RWVar _ _ => nil
  | RWApp _ op children =>
    op :: (fix visit (terms : list (rw_term K unit nat)) : list K :=
      match terms with
      | nil => nil
      | term :: rest => rw_facade_core_ops term ++ visit rest
      end) children
  end.

Definition rw_facade_input_ops {K} (rules : list (rewrite_rule K)) (terms : list (term K)) :
    list K :=
  flat_map (fun rule =>
    rw_facade_term_ops (rule_lhs rule) ++ rw_facade_term_ops (rule_rhs rule)) rules ++
  flat_map rw_facade_term_ops terms.

Definition rw_facade_binding_dimension {K} (bindings : list (term K)) : nat :=
  fold_right (fun term total => S (rw_facade_term_dimension term + total)) 1 bindings.

Fixpoint rw_facade_guard_control {K} (sub : nat -> term K) (program : rw_facade_guard_program K) :
    nat :=
  match program with
  | RWFacadeGuardReturn _ body => 64 + body
  | RWFacadeGuardLookup body index next =>
    64 + body + rw_facade_guard_control sub (next (sub index))
  end.

(** Every substitution index queried along the facade guard program is at most the bound. *)
Fixpoint rw_facade_guard_query_bound {K} (bound : nat) (sub : nat -> term K)
    (program : rw_facade_guard_program K) : Prop :=
  match program with
  | RWFacadeGuardReturn _ _ => True
  | RWFacadeGuardLookup _ index next =>
    index <= bound /\ rw_facade_guard_query_bound bound sub (next (sub index))
  end.

(** The facade envelope bounds listed operator encodings and weights. For listed rules,
    it bounds guard control and queries when bindings meet the dimension and operator
    encoding bounds. *)
Record rw_facade_foreign_envelope {K} (op : rw_queue_encoder_adapter K)
    (guard : rw_facade_guard_adapter K) (cost : K -> nat * nat)
    (rules : list (rewrite_rule K)) (operators : list K)
    (dimension width body weight : nat) : Prop := RwFacadeForeignEnvelope {
  (** Every listed operator satisfies the encoder width and work bounds. *)
  rw_facade_foreign_operator : forall k, In k operators -> rw_whole_encoder_fits op width body k;
  (** Each listed operator cost is at most weight and its callback work is at most body. *)
  rw_facade_foreign_weight : forall k, In k operators -> fst (cost k) <= weight /\ snd (cost k)
    <= body;
  (** For listed rules and bindings satisfying both dimension and operator-encoding bounds,
      guard control and visited query indices are at most body. *)
  rw_facade_foreign_guard : forall rule bindings,
    In rule rules -> rw_facade_binding_dimension bindings <= Nat.pow (S dimension) 16 ->
    Forall (fun term => Forall (rw_whole_encoder_fits op width body) (rw_facade_term_ops term))
      bindings ->
    rw_facade_guard_control (legacy_subst bindings) (rw_facade_guard_program_of guard rule)
      <= body /\
    rw_facade_guard_query_bound body (legacy_subst bindings)
      (rw_facade_guard_program_of guard rule)
}.

Definition rw_facade_whole_ceiling (fuel : N) (dimension width body weight : nat) : N :=
  (1099511627776 * (1 + fuel) * (1 + N.of_nat body) * N.pow (N.of_nat (S (dimension + width + body +
    weight))) (256 + 32 * N.pow (N.of_nat dimension) 4))%N.

(** The preparation work is bounded by a polynomial in the dimensions of the rules. *)
Definition rw_facade_prepare_bound_statement : Prop :=
  forall K (rules : list (rewrite_rule K)),
    let dimension :=
      fold_right (fun rule total => S (rw_facade_rule_dimension rule + total)) 1 rules in
    (N.of_nat (snd (rw_facade_prepare_atomic rules 0)) <=
      65536 * N.pow (N.of_nat (S dimension)) 16)%N.

(** Capture work is bounded by a polynomial in the provenance and captured-leaf dimensions. *)
Definition rw_facade_capture_bound_statement : Prop :=
  forall K (output : rw_tracked_output K unit nat nat),
    let '(leaves, work) := rw_facade_capture_atomic output in
    let dimension :=
      S (rw_facade_proof_dimension (rw_tracked_provenance (rw_tracked_final output)) +
        rw_facade_leaves_dimension leaves) in
    (N.of_nat work <= 65536 * N.pow (N.of_nat dimension) 16)%N.

(** A checked materialization run has work bounded by the ceiling for its proof, root,
    and result dimensions. *)
Definition rw_facade_materialize_bound_statement : Prop :=
  forall K (proof : rw_provenance K unit nat nat) root result work,
    rw_facade_checked_materialize_run proof root result work ->
    let dimension := S (rw_facade_proof_dimension proof + Pos.size_nat root +
      match result with
      | None => 1
      | Some steps => rw_facade_steps_dimension steps
      end) in
    (N.of_nat work <= rw_facade_whole_ceiling 0%N dimension 0 0 0)%N.

(** With agreeing operator encoding, guard laws, an optimizer run, and the foreign
    envelope, optimizer work is bounded by the whole-operation ceiling. *)
Definition rw_facade_optimizer_whole_bound_statement : Prop :=
  forall K (EK : encoding K) (op : rw_queue_encoder_adapter K) guard cost rules fuel seed result
    work dimension width body weight,
    (forall k, fst (rw_queue_encoder_run op k) = encode EK k) ->
    rw_facade_guard_program_laws guard ->
    rw_facade_optimizer_run EK op guard cost rules fuel seed result work dimension ->
    rw_facade_foreign_envelope op guard cost rules (rw_facade_input_ops rules [seed])
      dimension width body weight ->
    (N.of_nat work <= rw_facade_whole_ceiling (Npos fuel) dimension width body weight)%N.

Definition rw_facade_node_ops {K} (node : rw_node K unit nat) : list K :=
  match node with
  | RWNVar _ _ => nil
  | RWNApp _ op _ => [op]
  end.

Definition rw_facade_reason_ops {K} (reason : rw_evidence_reason K unit nat nat) : list K :=
  match reason with
  | RWEvidenceRule _ bindings =>
    flat_map (fun entry => rw_facade_core_ops (snd entry)) (Map.elements bindings)
  | _ => nil
  end.

Definition rw_facade_selected_ops {K} (rules : list (rewrite_rule K)) (seed output : term K) (legacy
    : rw_legacy_tracked_state K) : list K :=
  let state := rw_tracked_final (rw_legacy_core K legacy) in
  rw_facade_input_ops rules [seed; output] ++
  flat_map (fun entry => rw_facade_node_ops (snd (snd entry)))
    (Map.elements (rw_nodes (rw_index_base (rw_tracked_machine state)))) ++
  flat_map (fun entry => rw_facade_core_ops (rw_evidence_left (snd entry)) ++
    rw_facade_core_ops (rw_evidence_right (snd entry)) ++
    rw_facade_reason_ops (rw_evidence_reason_of (snd entry)))
    (Map.elements (rw_provenance_nodes (rw_tracked_provenance state))).

(** Selected reconstruction has a result, work, and dimension for every supplied state. *)
Definition rw_facade_selected_total_statement : Prop :=
  forall K (op : rw_queue_encoder_adapter K) guard rules seed (legacy : rw_legacy_tracked_state K)
    output,
    exists result work dimension,
      rw_facade_selected_run op guard rules seed legacy output result work dimension.

(** Two selected reconstruction runs on the same inputs have equal results, work, and dimensions. *)
Definition rw_facade_selected_unique_statement : Prop :=
  forall K (op : rw_queue_encoder_adapter K) guard rules seed (legacy : rw_legacy_tracked_state K)
    output first fw fd second sw sd,
    rw_facade_selected_run op guard rules seed legacy output first fw fd ->
    rw_facade_selected_run op guard rules seed legacy output second sw sd ->
    first = second /\ fw = sw /\ fd = sd.

(** Given a selected reconstruction run and foreign-operation envelope, its work is
    bounded by the ceiling for its complete dimension. *)
Definition rw_facade_selected_whole_bound_statement : Prop :=
  forall K (op : rw_queue_encoder_adapter K) guard rules seed
    (legacy : rw_legacy_tracked_state K) output result work dimension width body,
    rw_facade_selected_run op guard rules seed legacy output result work dimension ->
    let complete_dimension := S (dimension +
      fold_right (fun rule total => S (rw_facade_rule_dimension rule + total)) 1 rules) in
    rw_facade_foreign_envelope op guard (fun _ => (0, 0)) rules
      (rw_facade_selected_ops rules seed output legacy) complete_dimension width body 0 ->
    (N.of_nat work <= rw_facade_whole_ceiling 0%N complete_dimension width body 0)%N.

(** The natural adapter returns the natural encoding and its event work; the unit
    adapter returns the unit encoding with work 64. *)
Definition rw_facade_fixed_encoders_statement : Prop :=
  (forall index,
    fst (rw_queue_encoder_run rw_facade_nat_adapter index) = encode nat_encoding index /\
    snd (rw_queue_encoder_run rw_facade_nat_adapter index) =
      audit_nat_events_work (snd (audit_nat_encode index))) /\
  forall value,
    rw_queue_encoder_run rw_facade_unit_adapter value = (encode unit_encoding value, 64).
