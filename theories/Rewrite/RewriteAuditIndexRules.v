(** * RewriteAuditIndexRules

    This module audits guard evaluation, instantiation, and prepared rule-table operations.
    For example, looking up any position in an empty rule list returns None and work 64.
    Builds on: RewriteAuditIndexMembership and
    RewriteAuditQueueReference. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Rewrite Require Import RewriteAuditIndexMembership RewriteAuditQueueReference.
Import List.ListNotations.

Inductive rw_rp_guard_program (K Sort V H : Type) : Type :=
  | RPGuardReturn : bool -> nat -> rw_rp_guard_program K Sort V H
  | RPGuardLookup : nat -> H -> (option (rw_term K Sort V) -> rw_rp_guard_program K Sort V H) ->
      rw_rp_guard_program K Sort V H.
Arguments RPGuardReturn {K Sort V H}.
Arguments RPGuardLookup {K Sort V H}.

Fixpoint rw_rp_guard_plain {K Sort V H} (sub : rw_substitution K Sort V H)
    (program : rw_rp_guard_program K Sort V H) : bool :=
  match program with
  | RPGuardReturn answer _ => answer
  | RPGuardLookup _ h next => rw_rp_guard_plain sub (next (sub h))
  end.

Fixpoint rw_rp_guard_execute {K Sort V H} (hole : rw_queue_encoder_adapter H)
    (bindings : Map.t H (rw_term K Sort V)) (program : rw_rp_guard_program K Sort V H) :
    bool * nat * list (audit_map_event H (rw_term K Sort V) nat) :=
  match program with
  | RPGuardReturn answer body => (answer, 64 + body, nil)
  | RPGuardLookup body h next =>
    let '(binding, receipt) := audit_map_get (rw_external_encoding_events hole) h bindings in
    let '(answer, later_work, later) := rw_rp_guard_execute hole bindings (next binding) in
    (answer, 64 + body + audit_map_source_work rw_external_events_work receipt + later_work,
      receipt ++ later)
  end.

Record rw_rp_rule_callbacks (K Sort V H : Type) := RwRpRuleCallbacks {
  rw_rp_var_sort : V -> option Sort * nat;
  rw_rp_operator_shape : K -> list Sort -> Sort -> bool * nat;
  rw_rp_hole_sort : rw_rule K Sort V H -> H -> option Sort * nat;
  rw_rp_guard : rw_rule K Sort V H -> rw_rp_guard_program K Sort V H
}.
Arguments rw_rp_var_sort {K Sort V H}.
Arguments rw_rp_operator_shape {K Sort V H}.
Arguments rw_rp_hole_sort {K Sort V H}.
Arguments rw_rp_guard {K Sort V H}.

Fixpoint rw_rp_term_sorts {K Sort V} (terms : list (rw_term K Sort V)) : list Sort * nat :=
  match terms with
  | nil => (nil, 64)
  | t :: rest =>
    let '(tail, work) := rw_rp_term_sorts rest in
    (rw_sort t :: tail, 128 + work)
  end.

Fixpoint rw_rp_type_atomic {K Sort V H} (sort : rw_queue_encoder_adapter Sort)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (term : rw_term K Sort V) : bool * nat :=
  match term with
  | RWVar ty v =>
    let '(declared, callback_work) := rw_rp_var_sort callbacks v in
    match declared with
    | None => (false, 64 + callback_work)
    | Some s =>
      let '(answer, work) := rw_ri_encoded_equal sort ty s in
      (answer, 64 + callback_work + work)
    end
  | RWApp ty op children =>
    let fix visit (terms : list (rw_term K Sort V)) : bool * nat :=
      match terms with
      | nil => (true, 64)
      | t :: rest =>
        let '(head, hw) := rw_rp_type_atomic sort callbacks t in
        let '(tail, tw) := visit rest in
        (head && tail, 64 + hw + tw)
      end in
    let '(typed, type_work) := visit children in
    let '(sorts, sort_work) := rw_rp_term_sorts children in
    let '(shape, callback_work) := rw_rp_operator_shape callbacks op sorts ty in
    (typed && shape, 64 + type_work + sort_work + callback_work)
  end.

Fixpoint rw_rp_sub_check_atomic {K Sort V H} (sort : rw_queue_encoder_adapter Sort)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rule : rw_rule K Sort V H) (holes : list H) (bindings : Map.t H (rw_term K Sort V)) :
    bool * nat :=
  match holes with
  | nil => (true, 64)
  | h :: rest =>
    let '(declared, callback_work) := rw_rp_hole_sort callbacks rule h in
    let '(head, head_work) :=
      match declared with
      | None => (false, 64 + callback_work)
      | Some ty =>
        let '(binding, trace) :=
          audit_map_get (rw_external_encoding_events hole) h bindings in
        let lookup_work := audit_map_source_work rw_external_events_work trace in
        match binding with
        | None => (false, 64 + callback_work + lookup_work)
        | Some term =>
          let '(same_sort, comparison_work) := rw_ri_encoded_equal sort (rw_sort term) ty in
          if same_sort then
            let '(typed, type_work) := rw_rp_type_atomic sort callbacks term in
            (typed, 64 + callback_work + lookup_work + comparison_work + type_work)
          else (false, 64 + callback_work + lookup_work + comparison_work)
        end
      end in
    let '(tail, tail_work) := rw_rp_sub_check_atomic sort hole callbacks rule rest bindings in
    (head && tail, 64 + head_work + tail_work)
  end.

Definition rw_rp_guard_atomic {K Sort V H} (hole : rw_queue_encoder_adapter H)
    (callbacks : rw_rp_rule_callbacks K Sort V H) (rule : rw_rule K Sort V H)
    (bindings : Map.t H (rw_term K Sort V)) : bool * nat :=
  let '(answer, work, _) := rw_rp_guard_execute hole bindings (rw_rp_guard callbacks rule) in
  (answer, 64 + work).

Fixpoint rw_rp_instantiate_atomic {K Sort V H} (hole : rw_queue_encoder_adapter H)
    (bindings : Map.t H (rw_term K Sort V)) (pattern : rw_pattern K Sort V H) :
    option (rw_term K Sort V) * nat :=
  match pattern with
  | RWHole _ h =>
    let '(out, trace) := audit_map_get (rw_external_encoding_events hole) h bindings in
    (out, 64 + audit_map_source_work rw_external_events_work trace)
  | RWPVar ty v => (Some (RWVar ty v), 64)
  | RWPApp ty op children =>
    let fix visit (ps : list (rw_pattern K Sort V H)) : option (list (rw_term K Sort V)) * nat :=
      match ps with
      | nil => (Some nil, 64)
      | p :: rest =>
        let '(head, hw) := rw_rp_instantiate_atomic hole bindings p in
        match head with
        | None => (None, 64 + hw)
        | Some term =>
          let '(tail, tw) := visit rest in
          (option_map (fun ts => term :: ts) tail, 64 + hw + tw)
        end
      end in
    let '(args, work) := visit children in (option_map (RWApp ty op) args, 64 + work)
  end.

Fixpoint rw_rp_rule_lookup {K Sort V H} (rules : list (rw_rule K Sort V H)) (position : nat) :
    option (rw_rule K Sort V H) * nat :=
  match rules with
  | nil => (None, 64)
  | rule :: rest =>
    match position with
    | 0 => (Some rule, 64)
    | S p =>
      let '(out, work) := rw_rp_rule_lookup rest p in (out, 64 + work)
    end
  end.

Fixpoint rw_rp_rule_table_atomic {K Sort V H} (rules : list (rw_rule K Sort V H)) (index : nat) :
    Map.t nat (rw_rule K Sort V H) * nat :=
  match rules with
  | nil => (Map.empty, 64)
  | rule :: rest =>
    let '(table, tail_work) := rw_rp_rule_table_atomic rest (S index) in
    let '(out, trace) := audit_map_set audit_nat_encode index rule table in
    (out, 64 + tail_work + audit_map_source_work audit_nat_events_work trace)
  end.

Definition rw_rp_rule_body_gate_atomic {K Sort V H} (sort : rw_queue_encoder_adapter Sort)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rule : rw_rule K Sort V H) (attempt : rw_attempt K Sort V H) :
    option (rw_term K Sort V * rw_term K Sort V) * nat :=
  let bindings := rw_attempt_sub attempt in
  let '(typed, type_work) :=
    rw_rp_sub_check_atomic sort hole callbacks rule (rw_holes rule) bindings in
  let '(guard, guard_work) := rw_rp_guard_atomic hole callbacks rule bindings in
  let prefix := 64 + type_work + guard_work in
  if typed && guard then
    let '(lhs, lw) := rw_rp_instantiate_atomic hole bindings (rw_lhs rule) in
    match lhs with
    | None => (None, prefix + lw)
    | Some left_term =>
      let '(rhs, rw) := rw_rp_instantiate_atomic hole bindings (rw_rhs rule) in
      (option_map (fun right_term => (left_term, right_term)) rhs, prefix + lw + rw)
    end
  else (None, prefix).

Definition rw_rp_rule_gate_prepared_atomic {K Sort V H} (sort : rw_queue_encoder_adapter Sort)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (table : Map.t nat (rw_rule K Sort V H)) (attempt : rw_attempt K Sort V H) :
    option (rw_term K Sort V * rw_term K Sort V) * nat :=
  let '(found, lookup) := audit_map_get audit_nat_encode (rw_attempt_rule attempt) table in
  let prefix := 64 + audit_map_source_work audit_nat_events_work lookup in
  match found with
  | None => (None, prefix)
  | Some rule =>
    let '(out, work) := rw_rp_rule_body_gate_atomic sort hole callbacks rule attempt in
    (out, prefix + work)
  end.

Definition rw_rp_rule_gate_atomic {K Sort V H} (sort : rw_queue_encoder_adapter Sort)
    (hole : rw_queue_encoder_adapter H) (callbacks : rw_rp_rule_callbacks K Sort V H)
    (rules : list (rw_rule K Sort V H)) (attempt : rw_attempt K Sort V H) :
    option (rw_term K Sort V * rw_term K Sort V) * nat :=
  let '(table, preparation_work) := rw_rp_rule_table_atomic rules 0 in
  let '(out, work) := rw_rp_rule_gate_prepared_atomic sort hole callbacks table attempt in
  (out, 64 + preparation_work + work).

(** Lookup in the erased prepared rule table returns the rule at that list index. *)
Definition rw_rp_rule_table_erases_statement : Prop :=
  forall K Sort V H (rules : list (rw_rule K Sort V H)) index,
    Map.get nat_encoding index (fst (rw_rp_rule_table_atomic rules 0)) = nth_error rules index.

(** When the hole adapter agrees with its encoding, erasing instantiation work yields
    plain instantiation using the binding map. *)
Definition rw_rp_instantiate_erases_statement : Prop :=
  forall K Sort V H (EH : encoding H) (hole : rw_queue_encoder_adapter H) bindings pattern,
    (forall h, fst (rw_queue_encoder_run hole h) = encode EH h) ->
    @fst (option (rw_term K Sort V)) nat (rw_rp_instantiate_atomic hole bindings pattern) =
      rw_instantiate (fun h => Map.get EH h bindings) pattern.

(** The same finite guard program agrees with the actual guard for every substitution. *)
Definition rw_rp_guard_adapter_laws {K Sort V H} (callbacks : rw_rp_rule_callbacks K Sort V H) :
    Prop :=
  forall rule sub, rw_rp_guard_plain sub (rw_rp_guard callbacks rule) = rw_condition rule sub.
