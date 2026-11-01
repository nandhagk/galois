(** * Adequacy of complete clobber search

    Setup, indexed search and root materialization preserve the plain clobber result.
    For example, an unlisted version is read as an empty successor row.
    Builds on: indexed walk and search adequacy and finite-set enumeration. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditMapAdequacy CollectionsAuditElements
  CollectionsAuditElementsAdequacy.
From Galois.Graph Require Import GraphPrepare.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFrontier AnalysesMemoryWalk
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryEncodingAdequacy AnalysesAuditMemoryDistinct
  AnalysesAuditMemoryDistinctAdequacy AnalysesAuditMemorySearch AnalysesAuditMemorySearchAdequacy
  AnalysesAuditMemoryInputBudget AnalysesAuditMemoryInputBudgetAdequacy
  AnalysesAuditMemorySharedBudget AnalysesAuditMemorySharedBudgetAdequacy
  AnalysesAuditMemorySearchInputBudget AnalysesAuditMemorySearchInputBudgetAdequacy
  AnalysesAuditMemoryWalkIndex AnalysesAuditMemoryWalkIndexAdequacy
  AnalysesAuditMemoryClobbersSource.
Import List.ListNotations.

(** * Complete search and materialization *)

(** The indexed successor adapter returns the plain row, including a missing row. *)
Lemma audit_walk_successors_erases N E CN CE (EN : encoding N) (EE : encoding E)
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (rows : Map.t (memory_version N E) (list (memory_version N E))) version :
  (forall n, fst (node_enc n) = encode EN n) ->
  (forall e, fst (edge_enc e) = encode EE e) ->
  fst (audit_walk_successors node_enc edge_enc rows version) =
    index_edges (memory_frontier_version_encoding EN EE) rows version.
Proof.
  intros Hnode Hedge.
  apply audit_walk_predecessors_erases.
  apply audit_memory_version_encode_erases; assumption.
Qed.

(** The full counted result erases to the plain clobber result with the same fuel. *)
Theorem audit_memory_clobbers_source_erases : audit_memory_clobbers_source_erases_statement.
Proof.
  intros N E T CN CE SE OE TE FE PE BE EN EE ET node_enc edge_enc site_enc out target effects
    operand before g original mg scope start fuel Hnode Hedge Hsite Hout Htarget Heffects Hoperand
    Hbefore.
  pose proof (audit_memory_walk_index_erases N E T CN CE SE OE TE FE PE BE EN EE ET node_enc
    edge_enc site_enc out target effects operand before g original mg scope Hnode Hedge Hsite Hout
    Htarget Heffects Hoperand Hbefore) as Hindex.
  pose proof (audit_memory_search_run_erases (memory_version N E)
    (audit_memory_version_event N E CN CE)
    (audit_map_event (memory_version N E) (list (memory_version N E))
      (audit_memory_version_event N E CN CE))
    (memory_frontier_version_encoding EN EE) (audit_memory_version_encode node_enc edge_enc)
    (audit_walk_successors node_enc edge_enc
      (audit_walk_index_value (audit_memory_walk_index_counted EN node_enc edge_enc site_enc out
        target effects operand before g mg scope))) fuel (memory_search_start start)) as Hsearch.
  assert (Hencode : forall v, fst (audit_memory_version_encode node_enc edge_enc v) =
    encode (memory_frontier_version_encoding EN EE) v).
  { intro v; apply audit_memory_version_encode_erases; assumption. }
  specialize (Hsearch Hencode).
  rewrite Hindex in Hsearch.
  assert (Hnext : forall v,
    fst (audit_walk_successors node_enc edge_enc
      (memory_walk_index EN EE ET g original mg scope) v) =
    memory_walk_successors EN EE ET g original mg scope v).
  { intro v; unfold memory_walk_successors.
    apply audit_walk_successors_erases; assumption. }
  rewrite (memory_search_run_next_agrees (memory_frontier_version_encoding EN EE)
    (fun v => fst (audit_walk_successors node_enc edge_enc
      (memory_walk_index EN EE ET g original mg scope) v))
    (memory_walk_successors EN EE ET g original mg scope) fuel (memory_search_start start) Hnext)
    in Hsearch.
  unfold audit_memory_clobbers_source_counted, memory_clobbers.
  destruct (audit_memory_walk_index_counted EN node_enc edge_enc site_enc out target effects operand
    before g mg scope) as [rows table_events prepare_events index_events] eqn:Hsetup.
  destruct (audit_memory_search_run (audit_memory_version_encode node_enc edge_enc)
    (audit_walk_successors node_enc edge_enc rows) fuel (memory_search_start start))
    as [state search_events] eqn:Hrun.
  cbn in Hindex.
  pose proof Hrun as Hrun_indexed.
  rewrite Hindex in Hrun_indexed.
  rewrite Hrun_indexed in Hsearch; cbn in Hsearch.
  pose proof (audit_finset_elements_erases (memory_version N E) (memory_search_roots state))
    as Helements.
  destruct (audit_finset_elements (memory_search_roots state)) as [roots events] eqn:Helementsrun.
  cbn in Helements.
  pose proof (audit_memory_distinct_erases (memory_version N E)
    (audit_memory_version_event N E CN CE) (audit_memory_version_encode node_enc edge_enc)
    (memory_frontier_version_encoding EN EE) (roots ++ memory_search_todo state)) as Hdistinct.
  specialize (Hdistinct (fun v _ => Hencode v)).
  destruct (audit_memory_distinct (audit_memory_version_encode node_enc edge_enc)
    (roots ++ memory_search_todo state)) as [result distinct_events] eqn:Hdistinctrun.
  cbn in Hdistinct.
  cbn [audit_walk_index_value].
  rewrite Hrun, Helementsrun, Hdistinctrun; cbn [audit_clobbers_source_result].
  unfold memory_search_result; rewrite <- Hsearch, <- Helements, <- Hdistinct.
  reflexivity.
Qed.

(** Indexed successor reads pay the actual encoded-version map lookup. *)
Lemma audit_walk_successors_work_bound N E CN CE (node_enc : N -> positive * list CN)
    (edge_enc : E -> positive * list CE) node_work edge_work node_budget edge_budget
    (rows : Map.t (memory_version N E) (list (memory_version N E))) version :
  (forall n, node_work (snd (node_enc n)) <= node_budget n) ->
  (forall e, edge_work (snd (edge_enc e)) <= edge_budget e) ->
  audit_map_source_work (audit_memory_version_work node_work edge_work)
    (snd (audit_walk_successors node_enc edge_enc rows version)) <=
  audit_search_read_input_budget (audit_memory_version_encode node_enc edge_enc)
    (audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget) version.
Proof.
  intros Hnode Hedge.
  pose proof (audit_memory_version_input_bound N E CN CE node_enc edge_enc node_work edge_work
    node_budget edge_budget version Hnode Hedge) as Hkey.
  pose proof (audit_map_get_source_work_bound (memory_version N E) (list (memory_version N E))
    (audit_memory_version_event N E CN CE) (audit_memory_version_encode node_enc edge_enc)
    (audit_memory_version_work node_work edge_work) version rows) as Hread.
  unfold audit_walk_successors, audit_search_read_input_budget.
  destruct (audit_map_get (audit_memory_version_encode node_enc edge_enc) version rows)
    as [found calls]; cbn [snd] in Hread |- *; lia.
Qed.

(** Complete clobber work covers setup, actual search calls and output materialization. *)
Theorem audit_memory_clobbers_whole_input_bound : audit_memory_clobbers_whole_input_bound_statement.
Proof.
  intros N E T CN CE SE OE TE FE PE BE EN node_enc edge_enc site_enc out target effects operand
    before node_work edge_work site_work out_work target_work effect_work operand_work before_work
    node_budget edge_budget site_budget out_budget target_budget effect_budget operand_budget
    before_budget g mg scope start fuel Hnode Hout Htarget Hnodework Hedgework Hsitework Houtwork
    Htargetwork Heffectwork Hoperandwork Hbeforework.
  pose proof (audit_memory_walk_index_whole_input_bound N E T CN CE SE OE TE FE PE BE EN node_enc
    edge_enc site_enc out target effects operand before node_work edge_work site_work out_work
    target_work effect_work operand_work before_work node_budget edge_budget site_budget out_budget
    target_budget effect_budget operand_budget before_budget g mg scope Hnode Hout Htarget Hnodework
    Hedgework Hsitework Houtwork Htargetwork Heffectwork Hoperandwork Hbeforework) as Hsetup.
  set (setup := audit_memory_walk_index_counted EN node_enc edge_enc site_enc out target effects
    operand before g mg scope).
  set (enc := audit_memory_version_encode node_enc edge_enc).
  set (key_work := @audit_memory_version_work N E CN CE node_work edge_work).
  set (key_budget := audit_memory_version_input_budget node_enc edge_enc node_budget edge_budget).
  set (next := audit_walk_successors node_enc edge_enc (audit_walk_index_value setup)).
  set (next_work := @audit_map_source_work (memory_version N E) (list (memory_version N E))
    (audit_memory_version_event N E CN CE) key_work).
  assert (Hkey : forall v, key_work (snd (enc v)) <= key_budget v).
  { intro v; unfold key_work, enc, key_budget.
    apply audit_memory_version_input_bound; assumption. }
  assert (Hnext : forall v, next_work (snd (next v)) <= audit_search_read_input_budget enc
    key_budget v).
  { intro v; unfold next_work, next, enc, key_budget, key_work.
    apply audit_walk_successors_work_bound; assumption. }
  pose proof (audit_search_whole_input_bound (memory_version N E)
    (audit_memory_version_event N E CN CE)
    (audit_map_event (memory_version N E) (list (memory_version N E))
      (audit_memory_version_event N E CN CE)) enc next key_work next_work key_budget
    (audit_search_read_input_budget enc key_budget) fuel (memory_search_start start) Hkey Hnext)
    as Hsearch.
  destruct (audit_memory_search_run enc next fuel (memory_search_start start)) as [state events]
    eqn:Hrun; cbn [snd] in Hsearch.
  pose proof (audit_finset_elements_work_bound (memory_version N E) (memory_search_roots state))
    as Helements.
  pose proof (audit_finset_elements_erases (memory_version N E) (memory_search_roots state))
    as Hroots.
  destruct (audit_finset_elements (memory_search_roots state)) as [roots element_events]
    eqn:Helements_run; cbn [fst snd] in Helements, Hroots.
  pose proof (audit_memory_distinct_source_bound (memory_version N E)
    (audit_memory_version_event N E CN CE) enc key_work FinSet.empty
    (roots ++ memory_search_todo state)) as Hdistinct.
  pose proof (audit_memory_distinct_budget_input (memory_version N E)
    (audit_memory_version_event N E CN CE) enc key_work key_budget
    (roots ++ memory_search_todo state) Hkey) as Hdistinct_budget.
  unfold audit_memory_distinct in Hdistinct.
  destruct (audit_memory_distinct_from enc FinSet.empty (roots ++ memory_search_todo state))
    as [result distinct_events] eqn:Hdistinct_run; cbn [snd] in Hdistinct.
  unfold audit_memory_clobbers_full_source_work, audit_memory_clobbers_source_counted,
    audit_memory_clobbers_whole_input_budget.
  fold setup enc next.
  rewrite Hrun.
  rewrite Helements_run.
  unfold audit_memory_distinct; rewrite Hdistinct_run.
  cbn [audit_clobbers_source_index audit_clobbers_source_search audit_clobbers_source_elements
    audit_clobbers_source_distinct audit_clobbers_source_roots fst snd].
  rewrite <- Hroots.
  unfold next_work, key_work, enc, key_budget, next, setup in Hsearch, Hdistinct, Hdistinct_budget.
  cbn [fst] in Hsearch, Hdistinct, Hdistinct_budget.
  unfold enc, next, setup.
  lia.
Qed.
