(** * Whole budgets for shared memory preparation

    These recurrences use original nodes, outgoing occurrences and indexed effect operands.
    For example, a duplicate edge pays another probe but constructs its effect row only once.
    Builds on: memory edge, distinctness, effect-row and result-index bodies. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesAuditMemoryDistinct AnalysesAuditMemoryEffects
  AnalysesAuditMemoryIndex AnalysesAuditMemoryTable.
Import List.ListNotations.

Fixpoint audit_memory_edges_input_budget {N E OE} (out : N -> list E * list OE)
    (budget : N -> nat) (nodes : list N) : nat :=
  match nodes with
  | [] => 1
  | node :: rest => 2 + length (fst (out node)) + budget node +
      audit_memory_edges_input_budget out budget rest
  end.

Fixpoint audit_memory_distinct_input_budget {K CE} (enc : K -> positive * list CE)
    (budget : K -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 10 + 2 * budget key + 21 * Pos.size_nat (fst (enc key)) +
      audit_memory_distinct_input_budget enc budget rest
  end.

Fixpoint audit_memory_index_input_budget {K CE} (enc : K -> positive * list CE)
    (key_budget value_budget : K -> nat) (keys : list K) : nat :=
  match keys with
  | [] => 1
  | key :: rest => 3 + key_budget key + 16 * Pos.size_nat (fst (enc key)) + value_budget key +
      audit_memory_index_input_budget enc key_budget value_budget rest
  end.

Definition audit_memory_row_input_budget {E T FE}
    (effects : E -> list (memory_effect T) * list FE) (budget : E -> nat) (edge : E) : nat :=
  2 + budget edge + audit_memory_effects_budget 0 (fst (effects edge)).

Definition audit_memory_table_input_budget {N E T CE OE FE}
    (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
    (effects : E -> list (memory_effect T) * list FE)
    (edge_budget : E -> nat) (out_budget : N -> nat) (effect_budget : E -> nat)
    (nodes : list N) : nat :=
  let edges := fst (audit_memory_edges out nodes) in
  let unique := fst (audit_memory_distinct edge_enc edges) in
  3 + audit_memory_edges_input_budget out out_budget nodes +
    audit_memory_distinct_input_budget edge_enc edge_budget edges +
    audit_memory_index_input_budget edge_enc edge_budget
      (audit_memory_row_input_budget effects effect_budget) unique.

(** Encoder, outgoing and effect budgets bound the complete indexed effect-table construction. *)
Definition audit_memory_table_whole_input_bound_statement : Prop :=
  forall N E T CE OE FE (edge_enc : E -> positive * list CE) (out : N -> list E * list OE)
      (effects : E -> list (memory_effect T) * list FE)
      edge_work out_work effect_work edge_budget out_budget effect_budget nodes,
    (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
    (forall n, out_work (snd (out n)) <= out_budget n) ->
    (forall e, effect_work (snd (effects e)) <= effect_budget e) ->
    audit_memory_table_work edge_work out_work effect_work
      (snd (audit_memory_effect_table edge_enc out effects nodes)) <=
      audit_memory_table_input_budget edge_enc out effects edge_budget out_budget effect_budget
        nodes.

Example audit_shared_duplicate_distinct_budget :
  audit_memory_distinct_input_budget (fun p : positive => (p, @nil unit))
    (fun _ => 1) [1%positive; 1%positive] = 67.
Proof.
  reflexivity.
Qed.
