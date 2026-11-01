(** * Adequacy of shared memory table input budgets

    The input budget bounds the actual table construction using only callback charges.
    For example, duplicate edges each pay for a probe even when only one row is built.
    Builds on: AnalysesAuditMemorySharedBudget and the component adequacy proofs. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesAuditMemoryDistinct AnalysesAuditMemoryEffects
  AnalysesAuditMemoryIndex AnalysesAuditMemoryTable AnalysesAuditMemorySharedBudget
  AnalysesAuditMemoryEffectsAdequacy AnalysesAuditMemoryTableAdequacy.

(** Outgoing callback bounds lift to the edge traversal. *)
Lemma audit_memory_edges_budget_input N E OE (out : N -> list E * list OE) work budget nodes :
  (forall n, work (snd (out n)) <= budget n) ->
  audit_memory_edges_budget out work nodes <= audit_memory_edges_input_budget out budget nodes.
Proof.
  intro Hwork; induction nodes as [|node rest IH].
  - reflexivity.
  - cbn [audit_memory_edges_budget audit_memory_edges_input_budget].
    pose proof (Hwork node); lia.
Qed.

(** Per-key encoder bounds lift to the distinctness traversal. *)
Lemma audit_memory_distinct_budget_input K CE (enc : K -> positive * list CE) work budget keys :
  (forall k, work (snd (enc k)) <= budget k) ->
  audit_memory_distinct_budget enc work keys <= audit_memory_distinct_input_budget enc budget keys.
Proof.
  intro Hwork; induction keys as [|key rest IH].
  - reflexivity.
  - cbn [audit_memory_distinct_budget audit_memory_distinct_input_budget].
    pose proof (Hwork key); lia.
Qed.

(** Per-key encoder and row bounds lift to tail-first indexing. *)
Lemma audit_memory_index_budget_input K A CE VE (enc : K -> positive * list CE)
    (value : K -> A * list VE) key_work value_work key_budget value_budget keys :
  (forall k, key_work (snd (enc k)) <= key_budget k) ->
  (forall k, value_work (snd (value k)) <= value_budget k) ->
  audit_memory_index_budget enc value key_work value_work keys <=
    audit_memory_index_input_budget enc key_budget value_budget keys.
Proof.
  intros Hkey Hvalue; induction keys as [|key rest IH].
  - reflexivity.
  - cbn [audit_memory_index_budget audit_memory_index_input_budget].
    pose proof (Hkey key); pose proof (Hvalue key); lia.
Qed.

(** The row budget includes the callback and its actual numeric row construction. *)
Lemma audit_memory_row_budget_input E T FE (effects : E -> list (memory_effect T) * list FE)
    work budget edge :
  work (snd (effects edge)) <= budget edge ->
  audit_memory_row_work work (snd (audit_memory_effect_row effects edge)) <=
    audit_memory_row_input_budget effects budget edge.
Proof.
  intro Hwork.
  unfold audit_memory_effect_row, audit_memory_row_input_budget.
  pose proof (audit_memory_effects_work_bound T 0 (fst (effects edge))) as Hrow.
  destruct (effects edge) as [items calls].
  cbn in Hwork, Hrow |- *.
  destruct (audit_memory_effects_from 0 items) as [row events].
  simpl in *; lia.
Qed.

(** Callback bounds imply the whole table budget for the actual intermediate edge lists. *)
Theorem audit_memory_table_whole_input_bound : audit_memory_table_whole_input_bound_statement.
Proof.
  intros N E T CE OE FE edge_enc out effects edge_work out_work effect_work
    edge_budget out_budget effect_budget nodes Henc Hout Heffect.
  pose proof (audit_memory_effect_table_source_bound N E T CE OE FE edge_enc out effects nodes
    edge_work out_work effect_work) as Htable.
  pose proof (audit_memory_edges_budget_input N E OE out out_work out_budget nodes Hout) as Hedges.
  unfold audit_memory_table_budget in Htable.
  unfold audit_memory_table_input_budget.
  set (edges := fst (audit_memory_edges out nodes)) in *.
  set (unique := fst (audit_memory_distinct edge_enc edges)) in *.
  pose proof (audit_memory_distinct_budget_input E CE edge_enc edge_work edge_budget edges Henc)
    as Hdistinct.
  pose proof (audit_memory_index_budget_input E _ CE _ edge_enc (audit_memory_effect_row effects)
    edge_work (audit_memory_row_work effect_work) edge_budget
    (audit_memory_row_input_budget effects effect_budget) unique Henc
    (fun e => audit_memory_row_budget_input E T FE effects effect_work effect_budget e (Heffect e)))
    as Hindex.
  lia.
Qed.
