(** * Same-execution operands and input loop budget

    Dimensions inspect actual data operands, never returned work or event counts.
    For example, queue dimensions include its real entries and encoded priorities.
    Builds on: the source captures and the finite-powerset termination height. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsHeap CollectionsAuditCost CollectionsAuditElements CollectionsAuditQueue.
From Galois.Order Require Import OrderLattice OrderPowerset.
From Galois.Fixpoint Require Import FixpointSystem FixpointWorklist FixpointSchedule
  FixpointAuditWorklist FixpointAuditTotal FixpointAuditScheduleWrapper.
From Galois.Rules Require Import RulesSyntax RulesStratify RulesCompile RulesSolve
  RulesAuditMaterializePrelude RulesAuditMaterializeDeltaTotal RulesAuditMaterializeTrace.
Import List.ListNotations.

(** * Operand dimensions and input budgets *)

Definition mat_relation_dimension {P} (prog : program P) facts (a : relation prog facts) : nat :=
  1 + audit_trie_nodes (proj1_sig a) +
    fold_right (fun row n => mat_tuple_size row + n) 0 (FinSet.elements (proj1_sig a)).

Definition mat_assignment_dimension {P} (prog : program P) facts
    (values : assignment P (relation prog facts)) : nat :=
  1 + audit_trie_nodes values +
    fold_right (fun entry n => mat_relation_dimension prog facts (snd entry) + n)
      0 (Map.elements values).

Definition mat_constraint_dimension {P} (prog : program P) (c : rconstraint P) : nat :=
  match c with
  | FromRule i p => 1 + i + Pos.size_nat (encode (penc prog) p)
  | FromFact p => 1 + Pos.size_nat (encode (penc prog) p)
  end.

Definition mat_queue_dimension {P} (prog : program P) (queue : PQueue.t (rconstraint P)) : nat :=
  let heap := PQueue.pending queue in
  1 + PQueue.pending_count queue + PQueue.live_count queue +
    length heap + length (PQueue.entries heap) + audit_trie_nodes (PQueue.live queue) +
    audit_queue_input_width (rconstraint_encoding (penc prog)) heap (PQueue.live queue) [] [].

Definition mat_engine_call_dimension {P} (prog : program P) facts
    (call : fx_declared_call P (rconstraint P) (relation prog facts)) : nat :=
  match call with
  | FxTarget c _ | FxRhs c _ => mat_constraint_dimension prog c
  | FxPriority _ priority => 1 + Pos.size_nat priority
  | FxWideningPoint _ _ => 1
  | FxContinuation _ value _ _ => mat_relation_dimension prog facts value
  | FxLeb a b _ => 1 + mat_relation_dimension prog facts a + mat_relation_dimension prog facts b
  | FxJoin a b out | FxWiden a b out =>
      1 + mat_relation_dimension prog facts a + mat_relation_dimension prog facts b +
        mat_relation_dimension prog facts out
  | FxGet _ code before raw _ =>
      1 + Pos.size_nat code + mat_assignment_dimension prog facts before +
      match raw with
      | None => 0
      | Some a => mat_relation_dimension prog facts a
      end
  | FxSet _ code value before after _ =>
      1 + Pos.size_nat code + mat_relation_dimension prog facts value +
        mat_assignment_dimension prog facts before + mat_assignment_dimension prog facts after
  | FxReaders _ code before raw _ =>
      1 + Pos.size_nat code + audit_trie_nodes before +
      match raw with
      | None => 0
      | Some cs => length cs
      end
  | FxPush priority c before after _ =>
      1 + Pos.size_nat priority + mat_constraint_dimension prog c +
        mat_queue_dimension prog before + mat_queue_dimension prog after
  | FxPop before result _ => mat_queue_dimension prog before +
      match result with
      | None => 1
      | Some (_, c, after) =>
          1 + mat_constraint_dimension prog c + mat_queue_dimension prog after
      end
  end.

Definition mat_engine_trace_dimension {P} (prog : program P) facts
    (events : audit_trace (fx_declared_call P (rconstraint P) (relation prog facts))) : nat :=
  fold_right (fun event n => Nat.max n (
    match event with
    | AuditCall call => mat_engine_call_dimension prog facts call
    | AuditArithmetic _ operands =>
        fold_right (fun value m => Nat.max (N.size_nat value) m) 1 operands
    | _ => 1
    end)) 1 events.

Definition mat_rpo_dimension {P} (run : fx_rpo_result P (rconstraint P) mat_frame) : nat :=
  1 + length (fx_rpo_reverse_input run) + length (fx_rpo_reverse_output run) +
    audit_trie_nodes (fx_rpo_positions run) + audit_trie_nodes (fx_rpo_heads run) +
    fold_right (fun entry n => Nat.max (Pos.size_nat (snd entry)) n) 1
      (Map.elements (fx_rpo_positions run)) + mat_width (mat_rpo_callback_frames run).

(** This mathematical input budget uses the actual finite-powerset height, without executing it. *)
Definition mat_naive_level_input_steps {P} (prog : program P) facts (st : stratification P) k
    : nat :=
  fx_total_join_step_bound (relation_lattice prog facts)
    (base_height (finite_powerset_height tuple_encoding (herbrand prog facts)
      (herbrand_nodup prog facts)))
    (stratum_static prog facts st (fun _ => FinSet.empty) k).

Fixpoint mat_naive_levels_input_steps {P} (prog : program P) facts (st : stratification P)
    (n : nat) : nat :=
  match n with
  | O => 1
  | S k => 1 + mat_naive_levels_input_steps prog facts st k +
      mat_naive_level_input_steps prog facts st k
  end.

Definition mat_naive_program_input_steps {P} (prog : program P) facts : nat :=
  match stratify prog with
  | None => 1
  | Some st => mat_naive_levels_input_steps prog facts st (count st)
  end.

(** The whole budget uses input syntax, an input loop bound and actual operand dimensions. *)
Definition mat_naive_whole_budget {P} (prog : program P) facts (operand_max : nat) : nat :=
  (N.to_nat 1000000000000000%N) * S (mat_input_dimension prog facts) *
    S (mat_naive_program_input_steps prog facts) * Nat.pow (S operand_max) 32.
