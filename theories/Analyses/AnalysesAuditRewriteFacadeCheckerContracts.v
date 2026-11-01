(** * AnalysesAuditRewriteFacadeCheckerContracts

    This module measures checker trace operands and states a whole-operation work bound.
    For example, the dimension assigned to a missing optional term is 1.
    Builds on: AnalysesAuditRewriteFacadeReference and
    AnalysesAuditRewriteFacadeWholeContracts. *)

From Stdlib Require Import List Bool PArith NArith PeanoNat Lia.

From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsUnionFind CollectionsAuditCost CollectionsAuditTrie
  CollectionsAuditEncoding CollectionsAuditPrimitive CollectionsAuditMap CollectionsAuditFinSet
  CollectionsAuditElements CollectionsAuditUnion CollectionsAuditMapTraverse
  CollectionsAuditUnionFind.
From Galois.Rewrite Require Import RewriteSyntax RewriteRules RewriteEquality RewriteEgraph
  RewriteIndex RewriteRebuild RewriteExtract RewriteRun RewriteMatch RewriteAnalysis.
From Galois.Analyses Require Import AnalysesEgraph.
From Galois.Analyses Require Import AnalysesAuditRewriteFacadeDimensions
  AnalysesAuditRewriteFacadeOptimizer AnalysesAuditRewriteFacadeReference
  AnalysesAuditRewriteFacadeSourceWork AnalysesAuditRewriteFacadeWholeContracts.
From Galois.Rewrite Require Import RewriteAuditIndexDimensions RewriteAuditQueueReference.
Import List.ListNotations.

Definition rw_facade_option_dimension {K} (value : option (term K)) : nat :=
  match value with
  | None => 1
  | Some term => rw_facade_term_dimension term
  end.

Definition rw_facade_path_dimension (path : list nat) : nat :=
  fold_right (fun index total => S (index + total)) 1 path.

Definition rw_facade_table_operand_dimension {A} (value_dimension : A -> nat) (trace : audit_trace
    (rw_facade_table_call A)) : nat :=
  fold_right (fun event largest => Nat.max largest
    (
      match event with
      | AuditCall (RWFacadeTableSet index value before after code _ _) =>
        S (index + value_dimension value + Pos.size_nat code +
        rw_whole_map_dimension (fun key => S key) value_dimension before +
        rw_whole_map_dimension (fun key => S key) value_dimension after)
      | AuditCall (RWFacadeTableGet index before output code _ _) =>
        S (index + Pos.size_nat code +
        rw_whole_map_dimension (fun key => S key) value_dimension before +
        match output with
        | None => 1
        | Some value => value_dimension value
        end)
      | _ => 1
      end)) 1 trace.

Definition rw_facade_guard_operand_dimension {K} (actions : list (rw_facade_guard_action K)) : nat
    :=
  fold_right (fun action largest => Nat.max largest
    (
      match action with
      | RWGuardExternal _ => 1
      | RWGuardSubstitution index term _ => S (index + rw_facade_term_dimension term)
      end)) 1 actions.

Definition rw_facade_gate_operand_dimension {K} (trace : audit_trace (rw_facade_gate_call K)) : nat
    :=
  fold_right (fun event largest => Nat.max largest
    (
      match event with
      | AuditCall (RWFacadeGuard rule bindings _ actions) => S (rw_facade_rule_dimension rule +
        rw_facade_binding_dimension bindings + rw_facade_guard_operand_dimension actions)
      | _ => 1
      end)) 1 trace.

Definition rw_facade_subst_operand_dimension {K} (trace : audit_trace (rw_facade_subst_call K)) :
    nat :=
  fold_right (fun event largest => Nat.max largest
    (
      match event with
      | AuditCall (RWFacadeNth bindings index output _) => S (index +
        rw_facade_binding_dimension bindings + rw_facade_option_dimension output)
      | _ => 1
      end)) 1 trace.

Definition rw_facade_code_operand_dimension {K} (trace : audit_trace (rw_facade_code_call K)) : nat
    :=
  fold_right (fun event largest => Nat.max largest
    (
      match event with
      | AuditCall (RWCodeOp _ code _) => S (Pos.size_nat code)
      | AuditCall (RWCodeNat index code _) => S (index + Pos.size_nat code)
      | AuditCall (RWCodeAppend first second output _) => S (rw_whole_ids_dimension first +
        rw_whole_ids_dimension second + rw_whole_ids_dimension output)
      | AuditCall (RWCodeLength length _) => S length
      | AuditCall (RWCodeList input code _) => S (rw_whole_ids_dimension input + Pos.size_nat code)
      | AuditCall (RWCodeEmbed input output _) => S (rw_facade_term_dimension input +
        rw_facade_core_dimension output)
      | _ => 1
      end)) 1 trace.

Definition rw_facade_eq_operand_dimension {K} (trace : audit_trace (rw_facade_eq_call K)) : nat :=
  fold_right (fun event largest => Nat.max largest
    (
      match event with
      | AuditCall (RWFacadeCode term code child) => S (rw_facade_term_dimension term +
        Pos.size_nat code + rw_facade_code_operand_dimension child)
      | AuditCall (RWFacadeEqBits first second _ _) => S (Pos.size_nat first + Pos.size_nat second)
      | _ => 1
      end)) 1 trace.

Definition rw_facade_step_operand_dimension {K} (trace : audit_trace (rw_facade_step_call K)) : nat
    :=
  fold_right (fun event largest => Nat.max largest
    (
      match event with
      | AuditCall (RWFacadeLookup index rule child) => S (index +
        match rule with
        | None => 1
        | Some rule => rw_facade_rule_dimension rule
        end +
        rw_facade_table_operand_dimension rw_facade_rule_dimension child)
      | AuditCall (RWFacadeGate rule bindings _ child) => S (rw_facade_rule_dimension rule +
        rw_facade_binding_dimension bindings + rw_facade_gate_operand_dimension child)
      | AuditCall (RWFacadeSubst source output child) => S (rw_facade_term_dimension source +
        rw_facade_term_dimension output + rw_facade_subst_operand_dimension child)
      | AuditCall (RWFacadePosition path input output _) => S (rw_facade_path_dimension path +
        rw_facade_term_dimension input + rw_facade_option_dimension output)
      | AuditCall (RWFacadeEqual first second _ child) => S (rw_facade_term_dimension first +
        rw_facade_term_dimension second + rw_facade_eq_operand_dimension child)
      | AuditCall (RWFacadeReplace path input target output _) => S (rw_facade_path_dimension path +
        rw_facade_term_dimension input + rw_facade_term_dimension target +
        rw_facade_option_dimension output)
      | _ => 1
      end)) 1 trace.

Definition rw_facade_replay_operand_dimension {K} (trace : audit_trace (rw_facade_replay_call K)) :
    nat :=
  fold_right (fun event largest => Nat.max largest
    (
      match event with
      | AuditCall (RWFacadeReplayStep input step output child) =>
        S (rw_facade_term_dimension input + rw_facade_step_dimension step +
        rw_facade_option_dimension output +
        rw_facade_step_operand_dimension child)
      | _ => 1
      end)) 1 trace.

Definition rw_facade_checker_operand_dimension {K} (trace : audit_trace (rw_facade_checker_call K))
    : nat :=
  fold_right (fun event largest => Nat.max largest
    (
      match event with
      | AuditCall (RWFacadeCheckerTable table child) => S (
        rw_whole_map_dimension (fun key => S key) rw_facade_rule_dimension table +
        rw_facade_table_operand_dimension rw_facade_rule_dimension child)
      | AuditCall (RWFacadeCheckerReplay input steps output child) => S (
        rw_facade_term_dimension input + rw_facade_steps_dimension steps +
        rw_facade_option_dimension output + rw_facade_replay_operand_dimension child)
      | AuditCall (RWFacadeCheckerEqual first second _ child) => S (rw_facade_term_dimension first +
        rw_facade_term_dimension second + rw_facade_eq_operand_dimension child)
      | _ => 1
      end)) 1 trace.

Definition rw_facade_steps_ops {K} (steps : list (rewrite_step K)) : list K :=
  flat_map (fun step => flat_map rw_facade_term_ops (step_subst step)) steps.

(** Under the foreign-operation envelope, the checker trace work is bounded by the
    whole-operation ceiling for its actual operand dimension. *)
Definition rw_facade_checker_whole_bound_statement : Prop :=
  forall K (op : rw_queue_encoder_adapter K) guard rules (input target : term K) steps width body,
    let '(_, trace) := rw_facade_checker_atomic (rw_external_encoding_events op) guard
      rules input target steps in
    let dimension := S (rw_facade_term_dimension input + rw_facade_term_dimension target +
      rw_facade_steps_dimension steps + rw_facade_checker_operand_dimension trace) in
    rw_facade_foreign_envelope op guard (fun _ => (0, 0)) rules
      (rw_facade_input_ops rules [input; target] ++ rw_facade_steps_ops steps)
      dimension width body 0 ->
    (N.of_nat (rw_facade_checker_source_work trace) <=
      rw_facade_whole_ceiling 0%N dimension width body 0)%N.
