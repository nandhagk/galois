(** * Saved phi operand source bridges

    These proofs connect the captured set and saved queries to the actual phi producer.
    For example, repeated queries use the same set built during output construction.
    Builds on: phi producer, query, and adapted source adequacy. *)

From Stdlib Require Import List PArith Lia.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditFinSet CollectionsAuditFinSetAdequacy.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryEncodingAdequacy
  AnalysesAuditMemoryPhiProducer AnalysesAuditMemoryPhiProducerAdequacy
  AnalysesAuditMemoryPhiConsumer AnalysesAuditMemoryPhiConsumerAdequacy
  AnalysesAuditMemoryPhiSetup AnalysesAuditMemoryPhiSetupAdequacy
  AnalysesAuditMemoryPhiAdaptedSource AnalysesAuditMemoryPhiAdaptedSourceAdequacy
  AnalysesAuditMemoryPhiOperandQuery AnalysesAuditMemoryPhiOperandQueryAdequacy.
Import List.ListNotations.

(** The terminal fold event contains the actual final persistent set. *)
Lemma audit_phi_set_fold_final K C (enc : K -> positive * list C) xs initial :
  In (AuditSetFold [] (fst (audit_finset_fold enc xs initial)))
    (snd (audit_finset_fold enc xs initial)).
Proof.
  revert initial.
  induction xs as [|x rest IH]; intro initial.
  - cbn [audit_finset_fold]; now left.
  - cbn [audit_finset_fold].
    destruct (audit_finset_add enc x initial) as [next calls].
    destruct (audit_finset_fold enc rest next) as [result events] eqn:Hfold.
    cbn [fst snd]. right. apply in_or_app. right.
    specialize (IH next). rewrite Hfold in IH. exact IH.
Qed.

(** The retained set is the actual final build state and matches output inventory. *)
Theorem audit_phi_operand_saved_index : audit_phi_operand_saved_index_statement.
Proof.
  intros N E CN CV EN EE node_enc version_enc old reps Hnode Hversion.
  cbn zeta.
  pose proof (audit_phi_output_keep_erases N E CN CV EN EE node_enc version_enc reps
    (memory_phis old) Hversion) as Hkeep.
  destruct (audit_phi_output_keep_phis EN EE node_enc version_enc reps (memory_phis old))
    as [kept events] eqn:Hkept.
  pose proof (audit_finset_of_list_erases N CN node_enc EN kept (fun n _ => Hnode n)) as Hset.
  pose proof (audit_phi_set_fold_final N CN node_enc kept FinSet.empty) as Hfinal.
  fold (audit_finset_of_list node_enc kept) in Hfinal.
  destruct (audit_finset_of_list node_enc kept) as [captured calls] eqn:Hcapture.
  cbn [fst snd] in Hkeep, Hset, Hfinal |- *.
  rewrite Hcapture; cbn.
  split.
  - unfold audit_phi_operand_output_index. now rewrite <- Hkeep, <- Hset.
  - split.
    + exact Hfinal.
    + split.
      * unfold audit_phi_producer_output_counted. rewrite Hkept, Hcapture.
        destruct (audit_phi_output_filter_nodes node_enc captured (memory_phis old)).
        destruct (audit_phi_output_filter_versions node_enc version_enc captured
          (memory_versions old)). cbn [snd]. apply in_or_app. right. now left.
      * intro n. change (FinSet.mem EN n captured = true <->
          In n (filter (fun k => FinSet.mem EN k (audit_phi_operand_output_index EN EE old reps))
            (memory_phis old))).
        unfold audit_phi_operand_output_index.
        rewrite <- Hkeep, <- Hset. rewrite filter_In.
        split.
        -- intro Hmem. split; [|exact Hmem].
           rewrite Hset in Hmem. apply FinSet.of_list_spec in Hmem. rewrite Hkeep in Hmem.
           now apply filter_In in Hmem as [Hinside _].
        -- intros [_ Hmem]. exact Hmem.
Qed.

(** Saved queries return the corresponding operand of the output constructor. *)
Theorem audit_phi_operand_output_saved_query : audit_phi_operand_output_saved_query_statement.
Proof.
  intros N E CN CV B EN EE node_enc version_enc base old reps Hnode Hversion Hbase.
  pose proof (audit_phi_output_keep_erases N E CN CV EN EE node_enc version_enc reps
    (memory_phis old) Hversion) as Hkeep.
  pose proof (audit_finset_of_list_erases N CN node_enc EN
    (fst (audit_phi_output_keep_phis EN EE node_enc version_enc reps (memory_phis old)))
    (fun n _ => Hnode n)) as Hset.
  cbn zeta. intro input.
  unfold audit_phi_operand_saved_query.
  rewrite (audit_phi_output_operand_erases N E CN CV B EN EE node_enc version_enc base
    (fun p => memory_operand old (fst p) (snd p)) reps _ input Hnode Hversion (Hbase input)).
  unfold audit_phi_producer_output. cbn [memory_operand]. now rewrite Hset, Hkeep.
Qed.

(** Saved queries agree with both the counted run and the public plain result. *)
Theorem audit_phi_operand_producer_saved_query : audit_phi_operand_producer_saved_query_statement.
Proof.
  intros N E T CN CE PE B EN EE node_enc edge_enc pred operand g effects mg
    Hnode Hedge Hpred Hoperand.
  assert (Hversion : forall v, fst (audit_memory_version_encode node_enc edge_enc v) =
    encode (memory_version_encoding EN EE) v).
  { intro v. apply audit_memory_version_encode_erases; assumption. }
  pose proof (audit_phi_producer_value_shape N E T CN CE PE B _ EN EE node_enc edge_enc
    pred operand (audit_memory_version_encode node_enc edge_enc) g effects mg) as [_ [_ Houtput]].
  pose proof (audit_memory_phi_producer_erases N E T CN CE PE B EN EE node_enc edge_enc
    pred operand g effects mg Hnode Hedge Hpred Hoperand) as [Herase _].
  cbn zeta in *.
  rewrite (audit_phi_output_counted_erases N E CN _ EN EE node_enc
    (audit_memory_version_encode node_enc edge_enc) mg _ Hnode Hversion) in Houtput.
  intro input.
  pose proof (audit_phi_operand_output_saved_query N E CN _ B EN EE node_enc
    (audit_memory_version_encode node_enc edge_enc) (fun p => operand (fst p) (snd p)) mg
    (audit_phi_run_representatives EN (audit_phi_produce EN EE node_enc edge_enc pred operand
      (audit_memory_version_encode node_enc edge_enc) g effects mg))
    Hnode Hversion (fun p => Hoperand (fst p) (snd p)) input) as Hsaved.
  rewrite <- Houtput in Hsaved.
  split; [exact Hsaved|now rewrite <- Herase].
Qed.

(** The public source bridge charges setup and the actual captured query once. *)
Theorem audit_phi_operand_public_source_bridge : audit_phi_operand_public_source_bridge_statement.
Proof.
  intros N E T CN CE OE TE B EN EE node_enc edge_enc out target operand
    node_work edge_work out_work target_work operand_work
    node_budget edge_budget out_budget target_budget operand_budget g effects mg
    node_source edge_source out_source target_source operand_source input
    Hnode Hedge Hout Htarget Hoperand Hnode_adapter Hedge_adapter Hout_adapter
    Htarget_adapter Hoperand_adapter.
  pose proof (audit_memory_phi_prune_whole_input_bound_adapted N E T CN CE OE TE B EN EE
    node_enc edge_enc out target operand node_work edge_work out_work target_work operand_work
    node_budget edge_budget out_budget target_budget operand_budget g effects mg
    node_source edge_source out_source target_source operand_source Hnode Hout Htarget
    Hnode_adapter Hedge_adapter Hout_adapter Htarget_adapter Hoperand_adapter) as Hwork.
  pose proof (audit_memory_phi_prune_counted_erases N E T CN CE OE TE B EN EE node_enc edge_enc
    out target operand g effects mg Hnode Hedge Hout Htarget Hoperand) as Herase.
  unfold audit_memory_phi_prune_counted in Hwork, Herase |- *.
  destruct (GraphAuditBase.audit_prepare_source_counted EN g
    (audit_phi_input_graph_callbacks node_enc out target)) as [base preparation].
  cbn zeta in *.
  destruct Herase as [Hbase [Houtput Hreps]].
  assert (Hpred : forall n, fst (audit_phi_predecessors_counted EN node_enc g base n) =
    pred_edges (prepare EN g) n).
  { intro n. rewrite Hbase. apply audit_phi_predecessors_erases. exact Hnode. }
  pose proof (audit_phi_operand_producer_saved_query N E T CN CE _ B EN EE node_enc edge_enc
    (audit_phi_predecessors_counted EN node_enc g base) operand g effects mg
    Hnode Hedge Hpred Hoperand input) as [_ Hquery].
  set (reps := audit_phi_run_representatives EN (audit_phi_produce EN EE node_enc edge_enc
    (audit_phi_predecessors_counted EN node_enc g base) operand
    (audit_memory_version_encode node_enc edge_enc) g effects mg)) in *.
  set (captured := fst (audit_finset_of_list node_enc
    (fst (audit_phi_output_keep_phis EN EE node_enc
      (audit_memory_version_encode node_enc edge_enc) reps (memory_phis mg))))) in *.
  pose proof (audit_phi_operand_query_adapted_source N E CN CE B node_enc edge_enc
    (fun p => operand (fst p) (snd p)) node_work edge_work operand_work
    node_budget edge_budget (fun p => operand_budget (fst p) (snd p))
    node_source edge_source operand_source reps captured input Hnode_adapter Hedge_adapter
    Hoperand_adapter)
    as [Hcallbacks [_ Hquerywork]].
  cbn zeta in Hquery, Hcallbacks, Hquerywork.
  split; [exact Hquery|]. split; [exact Hcallbacks|].
  unfold audit_phi_operand_saved_query. lia.
Qed.

(** The full query contract combines each independently proved obligation. *)
Theorem audit_phi_operand_query_contract : audit_phi_operand_query_contract_statement.
Proof.
  unfold audit_phi_operand_query_contract_statement.
  split; [exact audit_phi_output_operand_erases|].
  split; [exact audit_phi_operand_query_trace|].
  split; [exact audit_phi_operand_query_source_adequate|].
  split; [exact audit_phi_operand_query_whole_input_bound|].
  split; [exact audit_phi_operand_query_adapted_source|].
  split; [exact audit_phi_operand_saved_index|].
  split; [exact audit_phi_operand_output_saved_query|].
  split; [exact audit_phi_operand_producer_saved_query|].
  split; [exact audit_phi_operand_public_source_bridge|].
  exact audit_phi_operand_saved_queries_bound.
Qed.
