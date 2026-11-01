(** * Whole memo-walk operand recurrence

    This independent recurrence computes a budget from actual states and intermediate roots.
    For example, a completed memo hit pays its two probes and performs no successor expansion.
    Builds on: memo execution rules, concrete memory input budgets and collection dimensions. *)

From Stdlib Require Import List NArith PArith.
From Galois.Collections Require Import CollectionsMap CollectionsFinSet.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding.
From Galois.Collections Require Import CollectionsAuditFinSet CollectionsAuditMap
  CollectionsAuditElements CollectionsAuditEncoding CollectionsAuditEncoderBudget.
From Galois.Analyses Require Import AnalysesAuditMemoryRawNext AnalysesAuditMemoryInputBudget
  AnalysesAuditMemoryMemo.
Import List.ListNotations.

Fixpoint audit_memo_build_input_budget {N E CV}
    (enc : memory_version N E -> positive * list CV)
    (budget : memory_version N E -> nat) (roots : list (memory_version N E)) : nat :=
  match roots with
  | [] => 1
  | root :: rest => 3 + budget root + 16 * Pos.size_nat (fst (enc root)) +
      audit_memo_build_input_budget enc budget rest
  end.

Definition audit_memo_union_input_budget {N E CV}
    (enc : memory_version N E -> positive * list CV)
    (budget : memory_version N E -> nat) (left right : list (memory_version N E)) : nat :=
  let input := left ++ right in
  let set := fst (audit_finset_of_list enc input) in
  2 + length left + audit_memo_build_input_budget enc budget input +
    19 * audit_trie_nodes set + audit_trie_output_bits set + 6.

Section MemoBudget.
  Context {N E CV CK NE : Type}.
  Let V := memory_version N E.
  Let M := Map.t (positive * V) (memo_entry N E).
  Variable version_enc : V -> positive * list CV.
  Variable key_enc : (positive * V) -> positive * list CK.
  Variable scope : positive.
  Variable next : V -> list V * list NE.
  Variable version_budget : V -> nat.
  Variable key_budget : (positive * V) -> nat.
  Variable next_budget : V -> nat.

  Definition audit_memo_active_input_budget (v : V) : nat :=
    8 + version_budget v + 5 * Pos.size_nat (fst (version_enc v)).

  Definition audit_memo_lookup_input_budget (v : V) : nat :=
    7 + key_budget (scope, v) + 5 * Pos.size_nat (fst (key_enc (scope, v))).

  Definition audit_memo_store_input_budget (v : V) : nat :=
    4 + key_budget (scope, v) + 16 * Pos.size_nat (fst (key_enc (scope, v))).

  Definition audit_memo_add_active_input_budget (v : V) : nat :=
    4 + version_budget v + 16 * Pos.size_nat (fst (version_enc v)).

  Definition audit_memo_probe_input_budget (v : V) : nat :=
    audit_memo_active_input_budget v + audit_memo_lookup_input_budget v.

  (** The recurrence relates inputs and memo result, cache and credit endpoints to an
    input-derived budget without inspecting execution events. *)
  Inductive audit_memo_input_budget_run : FinSet.t V -> M -> V -> BinNums.N ->
      memory_clobber_result N E -> M -> BinNums.N -> nat -> Prop :=
    | AuditMemoBudgetActive : forall active memo v fuel,
        fst (audit_finset_mem version_enc v active) = true ->
        audit_memo_input_budget_run active memo v fuel
          (MemoryClobberResult [v] false) memo fuel (audit_memo_active_input_budget v)
    | AuditMemoBudgetDone : forall active memo v fuel roots,
        fst (audit_finset_mem version_enc v active) = false ->
        fst (audit_map_get key_enc (scope, v) memo) = Some (MemoDone roots) ->
        audit_memo_input_budget_run active memo v fuel
          (MemoryClobberResult roots true) memo fuel (audit_memo_probe_input_budget v)
    | AuditMemoBudgetBusy : forall active memo v fuel,
        fst (audit_finset_mem version_enc v active) = false ->
        fst (audit_map_get key_enc (scope, v) memo) = Some MemoBusy ->
        audit_memo_input_budget_run active memo v fuel
          (MemoryClobberResult [v] false) memo fuel (audit_memo_probe_input_budget v)
    | AuditMemoBudgetFuel : forall active memo v,
        fst (audit_finset_mem version_enc v active) = false ->
        fst (audit_map_get key_enc (scope, v) memo) = None ->
        audit_memo_input_budget_run active memo v 0%N
          (MemoryClobberResult [v] false) memo 0%N (audit_memo_probe_input_budget v)
    | AuditMemoBudgetTerminal : forall active memo v fuel,
        fst (audit_finset_mem version_enc v active) = false ->
        fst (audit_map_get key_enc (scope, v) memo) = None -> fst (next v) = [] ->
        audit_memo_input_budget_run active memo v (N.succ fuel)
          (MemoryClobberResult [v] true)
          (fst (audit_map_set key_enc (scope, v) (MemoDone [v]) memo)) fuel
          (audit_memo_probe_input_budget v + 2 + next_budget v + audit_memo_store_input_budget v)
    | AuditMemoBudgetBranch : forall active memo v fuel first rest result final remaining cost,
        fst (audit_finset_mem version_enc v active) = false ->
        fst (audit_map_get key_enc (scope, v) memo) = None -> fst (next v) = first :: rest ->
        audit_memo_children_input_budget_run
          (fst (audit_finset_add version_enc v active)) memo (first :: rest) fuel
          result final remaining cost ->
        audit_memo_input_budget_run active memo v (N.succ fuel) result
          (if clobber_complete result then
            fst (audit_map_set key_enc (scope, v) (MemoDone (clobber_roots result)) final)
           else final) remaining
          (audit_memo_probe_input_budget v + 2 + next_budget v +
           audit_memo_add_active_input_budget v + cost +
           if clobber_complete result then audit_memo_store_input_budget v else 0)
  (** The child recurrence threads memo and fuel while summing child and root-union budgets. *)
  with audit_memo_children_input_budget_run : FinSet.t V -> M -> list V -> BinNums.N ->
      memory_clobber_result N E -> M -> BinNums.N -> nat -> Prop :=
    | AuditMemoBudgetChildrenNil : forall active memo fuel,
        audit_memo_children_input_budget_run active memo [] fuel
          (MemoryClobberResult [] true) memo fuel 0
    | AuditMemoBudgetChildrenCons : forall active memo v vs fuel one memo' fuel'
        tail memo'' fuel'' first_cost tail_cost,
        audit_memo_input_budget_run active memo v fuel one memo' fuel' first_cost ->
        audit_memo_children_input_budget_run active memo' vs fuel' tail memo'' fuel'' tail_cost ->
        audit_memo_children_input_budget_run active memo (v :: vs) fuel
          (MemoryClobberResult
            (fst (audit_memo_union version_enc (clobber_roots one) (clobber_roots tail)))
            (andb (clobber_complete one) (clobber_complete tail))) memo'' fuel''
          (first_cost + tail_cost + audit_memo_union_input_budget version_enc version_budget
            (clobber_roots one) (clobber_roots tail)).

  (** Callback budgets yield an independent recurrence witness at the tree endpoints that bounds
      its source work. *)
  Definition audit_memo_whole_input_bound_at : Prop :=
    forall version_work key_work next_work,
      (forall v, version_work (snd (version_enc v)) <= version_budget v) ->
      (forall key, key_work (snd (key_enc key)) <= key_budget key) ->
      (forall v, next_work (snd (next v)) <= next_budget v) ->
      forall active memo v fuel result final remaining events,
      audit_memo_tree version_enc key_enc scope next active memo v fuel result final remaining
        events ->
      exists budget,
        audit_memo_input_budget_run active memo v fuel result final remaining budget /\
        audit_memo_source_work version_work key_work next_work events <= budget.

  (** A fixed input and intermediate result cannot select an arbitrary larger budget. *)
  Definition audit_memo_input_budget_deterministic_at : Prop :=
    forall active memo v fuel result final remaining first second,
      audit_memo_input_budget_run active memo v fuel result final remaining first ->
      audit_memo_input_budget_run active memo v fuel result final remaining second -> first =
        second.
End MemoBudget.

(** Per-input callback bounds yield a budget for the same tree endpoints and source work. *)
Definition audit_memo_whole_input_bound_statement : Prop :=
  forall N E CV CK NE version_enc key_enc scope next version_budget key_budget next_budget,
    @audit_memo_whole_input_bound_at N E CV CK NE version_enc key_enc scope next version_budget
      key_budget next_budget.

(** Fixed tree endpoints determine a unique input-derived budget. *)
Definition audit_memo_input_budget_deterministic_statement : Prop :=
  forall N E CV CK NE version_enc key_enc scope next version_budget key_budget next_budget,
    @audit_memo_input_budget_deterministic_at N E CV CK NE version_enc key_enc scope next
      version_budget key_budget next_budget.

(** For a memo-tree derivation and callback budgets, a recurrence witness at the same endpoints
    bounds scope encoding and tree source work. *)
Definition audit_memory_memo_whole_input_bound_statement : Prop :=
  forall N E T CN CE SE IE OE BE (node_enc : N -> positive * list CN)
      (edge_enc : E -> positive * list CE) (site_enc : T -> positive * list SE) table
      (incoming : N -> list E * list IE)
      (operand : N -> option E -> option (memory_version N E) * list OE)
      (before : E -> nat -> option (memory_version N E) * list BE)
      node_work edge_work site_work incoming_work operand_work before_work
      node_budget edge_budget site_budget incoming_budget operand_budget before_budget
      q active memo v fuel result final remaining events,
    (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall t, site_work (snd (site_enc t)) <= site_budget t) ->
    (forall n, incoming_work (snd (incoming n)) <= incoming_budget n) ->
    (forall n key, operand_work (snd (operand n key)) <= operand_budget n key) ->
    (forall e i, before_work (snd (before e i)) <= before_budget e i) ->
    let scope := audit_memory_scope_encode site_enc q in
    let version_enc := audit_memory_version_encode node_enc edge_enc in
    let key_enc := audit_memory_memo_key_encode node_enc edge_enc in
    let next := audit_memory_raw_next edge_enc site_enc table incoming operand before q in
    let version_budget :=
      audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget in
    let key_budget :=
      audit_memory_memo_key_input_budget node_enc edge_enc node_budget edge_budget in
    let next_budget := @audit_raw_next_input_budget N E T CE SE IE OE BE
      edge_enc site_enc table incoming before edge_budget site_budget
      incoming_budget operand_budget before_budget q in
    audit_memo_tree version_enc key_enc (fst scope) next active memo v fuel
      result final remaining events ->
    exists budget,
      audit_memo_input_budget_run version_enc key_enc (fst scope) next
        version_budget key_budget next_budget active memo v fuel result final remaining budget /\
      audit_memory_scope_work site_work (snd scope) +
        audit_memo_source_work (audit_memory_version_work node_work edge_work)
          (audit_memory_memo_key_work node_work edge_work)
          (audit_raw_next_source_work edge_work site_work incoming_work operand_work before_work)
          events <= audit_memory_scope_input_budget site_enc site_budget q + budget.

Example audit_memo_union_budget_nonempty :
  audit_memo_union_input_budget
    (@audit_memory_version_encode positive positive
      (audit_basic_encoding_event positive) (audit_basic_encoding_event positive)
      audit_positive_encode audit_positive_encode)
    (fun _ => 1) [MemoryLive] [] > 0.
Proof.
  vm_compute.
  repeat constructor.
Qed.
