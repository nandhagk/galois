(** * AnalysesAuditRewriteFacadePrepare

    Translates legacy rules and guards into prepared Rewrite rules and callbacks.
    For example, the legacy variable 2 becomes the hole numbered 2 with work 64.
    Builds on: AnalysesAuditRewriteFacadeReference and
    RewriteAuditIndexRules. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeMaterialize
  AnalysesAuditRewriteFacadeReference.
From Galois.Rewrite Require Import RewriteAuditIndexRules RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_facade_nat_adapter : rw_queue_encoder_adapter nat :=
  RwQueueEncoderAdapter (fun index =>
    let '(code, trace) := audit_nat_encode index in (code, audit_nat_events_work trace)).

Definition rw_facade_unit_adapter : rw_queue_encoder_adapter unit :=
  RwQueueEncoderAdapter (fun _ => (1%positive, 64)).

Fixpoint rw_facade_pattern_atomic {K} (source : term K) : rw_pattern K unit nat nat * nat :=
  match source with
  | TVar index => (RWHole tt index, 64)
  | TApp op children =>
    let fix visit (terms : list (term K)) : list (rw_pattern K unit nat nat) * nat :=
      match terms with
      | nil => (nil, 64)
      | t :: rest =>
        let '(head, hw) := rw_facade_pattern_atomic t in
        let '(tail, tw) := visit rest in (head :: tail, 64 + hw + tw)
      end in
    let '(patterns, work) := visit children in (RWPApp tt op patterns, 64 + work)
  end.

Fixpoint rw_facade_holes_atomic (occurrences : list nat) : (list nat * FinSet.t nat) * nat :=
  match occurrences with
  | nil => ((nil, FinSet.empty), 64)
  | index :: rest =>
    let '((holes, present), tail_work) := rw_facade_holes_atomic rest in
    let '(seen, lookup) := audit_finset_mem audit_nat_encode index present in
    if seen then
      ((holes, present), 64 + tail_work + audit_finset_source_work audit_nat_events_work lookup)
    else
      let '(next, insertion) := audit_finset_add audit_nat_encode index present in
      ((index :: holes, next), 64 + tail_work +
        audit_finset_source_work audit_nat_events_work lookup +
        audit_finset_source_work audit_nat_events_work insertion)
  end.

Record rw_facade_prepared_rule (K : Type) := RwFacadePreparedRule {
  rw_facade_original_rule : rewrite_rule K;
  rw_facade_core_rule : rw_rule K unit nat nat;
  rw_facade_hole_set : FinSet.t nat
}.
Arguments RwFacadePreparedRule {K}.
Arguments rw_facade_original_rule {K}.
Arguments rw_facade_core_rule {K}.
Arguments rw_facade_hole_set {K}.

Definition rw_facade_prepare_rule_atomic {K} (rule : rewrite_rule K) : rw_facade_prepared_rule K *
    nat :=
  let '(left_vars, lv) := rw_facade_vars (rule_lhs rule) in
  let '(right_vars, rv) := rw_facade_vars (rule_rhs rule) in
  let '(occurrences, append_trace) := rw_queue_append_atomic left_vars right_vars in
  let '((holes, present), hole_work) := rw_facade_holes_atomic occurrences in
  let '(lhs, lw) := rw_facade_pattern_atomic (rule_lhs rule) in
  let '(rhs, rw) := rw_facade_pattern_atomic (rule_rhs rule) in
  let core := RwRule K unit nat nat holes
    (fun index =>
      if existsb (Nat.eqb index) holes then Some tt else None) lhs rhs
    (fun sub => rule_side rule (legacy_total_sub sub)) in
  (RwFacadePreparedRule rule core present,
    64 + 64 * (audit_work lv + audit_work rv + audit_work append_trace) + hole_work + lw + rw).

Record rw_facade_prepared (K : Type) := RwFacadePrepared {
  rw_facade_rule_entries : list (nat * rw_facade_prepared_rule K);
  rw_facade_rule_table : Map.t nat (rw_facade_prepared_rule K);
  rw_facade_original_table : Map.t nat (rewrite_rule K);
  rw_facade_core_rules : list (rw_rule K unit nat nat)
}.
Arguments RwFacadePrepared {K}.
Arguments rw_facade_rule_entries {K}.
Arguments rw_facade_rule_table {K}.
Arguments rw_facade_original_table {K}.
Arguments rw_facade_core_rules {K}.

Fixpoint rw_facade_prepare_atomic {K} (rules : list (rewrite_rule K)) (index : nat) :
    rw_facade_prepared K * nat :=
  match rules with
  | nil => (RwFacadePrepared nil Map.empty Map.empty nil, 64)
  | rule :: rest =>
    let '(tail, tail_work) := rw_facade_prepare_atomic rest (S index) in
    let '(prepared, rule_work) := rw_facade_prepare_rule_atomic rule in
    let '(table, table_trace) := audit_map_set audit_nat_encode index prepared
      (rw_facade_rule_table tail) in
    let '(original, original_trace) := audit_map_set audit_nat_encode index rule
      (rw_facade_original_table tail) in
    (RwFacadePrepared ((index, prepared) :: rw_facade_rule_entries tail) table original
      (rw_facade_core_rule prepared :: rw_facade_core_rules tail),
      64 + tail_work + rule_work + audit_map_source_work audit_nat_events_work table_trace +
        audit_map_source_work audit_nat_events_work original_trace)
  end.

Fixpoint rw_facade_guard_plain {K} (sub : nat -> term K) (program : rw_facade_guard_program K) :
    bool :=
  match program with
  | RWFacadeGuardReturn answer _ => answer
  | RWFacadeGuardLookup _ index next => rw_facade_guard_plain sub (next (sub index))
  end.

(** Every facade guard program returns its source rule side condition for the substitution. *)
Definition rw_facade_guard_program_laws {K} (adapter : rw_facade_guard_adapter K) : Prop :=
  forall rule sub, rw_facade_guard_plain sub (rw_facade_guard_program_of adapter rule) = rule_side
    rule sub.

Definition rw_facade_guard_add_work {K} (work : nat) (program : rw_rp_guard_program K unit nat nat)
    : rw_rp_guard_program K unit nat nat :=
  match program with
  | RPGuardReturn answer body => RPGuardReturn answer (work + body)
  | RPGuardLookup body index next => RPGuardLookup (work + body) index next
  end.

Fixpoint rw_facade_lift_guard {K} (program : rw_facade_guard_program K) : rw_rp_guard_program K unit
    nat nat :=
  match program with
  | RWFacadeGuardReturn answer body => RPGuardReturn answer body
  | RWFacadeGuardLookup body index next =>
    RPGuardLookup body index (fun found =>
      let '(observed, projection_work) :=
        match found with
        | None => (TVar index, 64)
        | Some term => rw_facade_materialize_project_atomic term
        end in
      rw_facade_guard_add_work projection_work (rw_facade_lift_guard (next observed)))
  end.

Definition rw_facade_local_callbacks {K} (guard : rw_facade_guard_adapter K) (prepared :
    rw_facade_prepared_rule K) : rw_rp_rule_callbacks K unit nat nat :=
  RwRpRuleCallbacks K unit nat nat
    (fun _ => (Some tt, 64)) (fun _ _ _ => (true, 64))
    (fun _ index =>
      let '(present, trace) := audit_finset_mem audit_nat_encode index
        (rw_facade_hole_set prepared) in
      ((if present then Some tt else None),
        64 + audit_finset_source_work audit_nat_events_work trace))
    (fun _ => rw_facade_lift_guard
      (rw_facade_guard_program_of guard (rw_facade_original_rule prepared))).

(** Preparation produces translated rules and the original table; each prepared entry
    agrees with its source rule and records exactly its holes. *)
Definition rw_facade_prepare_agrees_statement : Prop :=
  forall K (rules : list (rewrite_rule K)),
    let '(prepared, _) := rw_facade_prepare_atomic rules 0 in
    rw_facade_core_rules prepared = map legacy_rule rules /\
    rw_facade_original_table prepared = legacy_list_table rules 0 /\
    forall index entry,
      Map.get nat_encoding index (rw_facade_rule_table prepared) = Some entry ->
      nth_error rules index = Some (rw_facade_original_rule entry) /\
      rw_facade_core_rule entry = legacy_rule (rw_facade_original_rule entry) /\
      forall hole, FinSet.mem nat_encoding hole (rw_facade_hole_set entry) =
        existsb (Nat.eqb hole) (rw_holes (rw_facade_core_rule entry)).
