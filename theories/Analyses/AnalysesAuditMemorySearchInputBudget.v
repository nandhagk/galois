(** * Independent binary-search input recurrence

    These budgets follow binary fuel halves and their actual intermediate search states.
    For example, a seen version pays a root insertion and performs no successor callback.
    Builds on: the fixed memory search source model and concrete key input budgets. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Analyses Require Import AnalysesMemoryWalk.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Analyses Require Import AnalysesAuditMemorySearch.
Import List.ListNotations.

Definition audit_search_read_input_budget {V CE} (enc : V -> positive * list CE)
    (budget : V -> nat) (v : V) : nat := 5 + budget v + 5 * Pos.size_nat (fst (enc v)).

Definition audit_search_write_input_budget {V CE} (enc : V -> positive * list CE)
    (budget : V -> nat) (v : V) : nat := 2 + budget v + 16 * Pos.size_nat (fst (enc v)).

Definition audit_search_step_input_budget {V CE NE} (enc : V -> positive * list CE)
    (next : V -> list V * list NE) (key_budget next_budget : V -> nat)
    (state : memory_search_state V) : nat :=
  match memory_search_todo state with
  | [] => 2
  | v :: _ =>
      2 + audit_search_read_input_budget enc key_budget v +
      match fst (audit_map_get enc v (memory_search_seen state)) with
      | Some _ => audit_search_write_input_budget enc key_budget v
      | None =>
          let successors := fst (next v) in
          audit_search_write_input_budget enc key_budget v + 2 + length successors + next_budget v +
          match successors with
          | [] => audit_search_write_input_budget enc key_budget v
          | _ :: _ => 0
          end
      end
  end.

Fixpoint audit_search_run_input_budget {V CE NE} (enc : V -> positive * list CE)
    (next : V -> list V * list NE) (key_budget next_budget : V -> nat)
    (fuel : positive) (state : memory_search_state V) : nat :=
  match memory_search_todo state with
  | [] => 2
  | _ :: _ =>
      match fuel with
      | xH => 2 + audit_search_step_input_budget enc next key_budget next_budget state
      | xO half =>
          let middle := fst (audit_memory_search_run enc next half state) in
          2 + audit_search_run_input_budget enc next key_budget next_budget half state +
            audit_search_run_input_budget enc next key_budget next_budget half middle
      | xI half =>
          let middle := fst (audit_memory_search_run enc next half state) in
          let after := fst (audit_memory_search_run enc next half middle) in
          2 + audit_search_run_input_budget enc next key_budget next_budget half state +
            audit_search_run_input_budget enc next key_budget next_budget half middle +
            audit_search_step_input_budget enc next key_budget next_budget after
      end
  end.

(** Per-input encoder and successor budgets bound the binary-fuel search execution. *)
Definition audit_search_whole_input_bound_statement : Prop :=
  forall V CE NE (enc : V -> positive * list CE) (next : V -> list V * list NE)
      work next_work key_budget next_budget fuel state,
    (forall v, work (snd (enc v)) <= key_budget v) ->
    (forall v, next_work (snd (next v)) <= next_budget v) ->
    audit_memory_search_source_work work next_work (snd (audit_memory_search_run enc next fuel
      state)) <=
      audit_search_run_input_budget enc next key_budget next_budget fuel state.

Example audit_search_empty_input_budget :
  audit_search_run_input_budget (fun p : positive => (p, @nil unit))
    (fun _ => ([], @nil unit)) (fun _ => 1) (fun _ => 1) 8%positive
    (MemorySearchState [] CollectionsMap.Map.empty 0 CollectionsFinSet.FinSet.empty true) = 2.
Proof.
  reflexivity.
Qed.
