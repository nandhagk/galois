(** * Computed phi pruning boundary observations

    These examples exercise actual rows, persistent resolution states and returned closures.
    For example, a conflicting row still evaluates the operand after the first unequal input.
    Builds on: the fixed phi models and their independent adequacy leaves. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditEncoding CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryInputBudget AnalysesAuditMemoryPhiInputBudget
  AnalysesAuditMemoryPhiState AnalysesAuditMemoryPhiRows
  AnalysesAuditMemoryPhiResolve
  AnalysesAuditMemoryPhiProducer AnalysesAuditMemoryPhiConsumer AnalysesAuditMemoryPhiSetup
  AnalysesAuditMemoryPhiRowsAdequacy AnalysesAuditMemoryPhiResolveAdequacy
  AnalysesAuditMemoryPhiProducerAdequacy AnalysesAuditMemoryPhiConsumerAdequacy
  AnalysesAuditMemoryPhiPrepareAdequacy AnalysesAuditMemoryPhiStateAdequacy
  AnalysesAuditMemoryPhiAdaptedSourceAdequacy AnalysesAuditMemoryPhiSetupAdequacy
  AnalysesAuditMemoryPhiPublicAdequacy AnalysesAuditMemoryPhiFacade
  AnalysesAuditMemoryPhiOperandQuery.
Import List.ListNotations.

(** * First-occurrence rows and missing keys *)

Example audmp_distinct_empty :
  fst (audit_phi_distinct_from audit_positive_encode FinSet.empty []) = [].
Proof.
  reflexivity.
Qed.

Example audmp_distinct_duplicate_keys :
  fst (audit_phi_distinct_from audit_positive_encode FinSet.empty
    [1%positive; 1%positive; 2%positive; 1%positive]) = [1%positive; 2%positive].
Proof.
  vm_compute; reflexivity.
Qed.

Definition audmp_operand (_ : positive) (key : option positive) :
    option (memory_version positive positive) * list unit :=
  match key with
  | None =>
    (Some MemoryLive, [tt])
  | Some 1%positive =>
    (None, [tt; tt])
  | Some n =>
    (Some (MemoryPhi n), [tt])
  end.

Example audmp_duplicate_predecessor_and_missing_operand :
  let run := @audit_phi_input_row positive positive unit
    (audit_basic_encoding_event positive) unit unit audit_positive_encode
    (fun _ => ([1%positive; 1%positive; 2%positive], [tt])) audmp_operand 1%positive in
  fst run = [(None, MemoryLive); (Some 2%positive, MemoryPhi 2%positive)] /\
    length (snd run) = 5.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_duplicate_nodes_and_missing_index_key :
  let run := audit_phi_input_rows audit_positive_encode audit_positive_encode
    (fun _ : positive => (@nil positive, @nil unit))
    (fun _ _ => (@None (memory_version positive positive), @nil unit))
    [1%positive; 1%positive] in
  Map.get positive_encoding 1%positive (fst run) = Some [] /\
    Map.get positive_encoding 2%positive (fst run) = None /\ length (snd run) = 8.
Proof.
  vm_compute; split; [reflexivity|split; reflexivity].
Qed.

(** * Resolution from arbitrary intermediate states *)

Definition audmp_dependency_graph : Graph.t positive (phi_dependency_edge positive positive) :=
  {| Graph.entries := [1%positive; 2%positive];
     Graph.nodes := [1%positive; 2%positive];
     Graph.out := fun _ => [];
     Graph.source := dependency_source;
     Graph.target := dependency_target |}.

Definition audmp_index
    (inputs : Map.t positive (list (option positive * memory_version positive positive)))
    (cycles : FinSet.t positive) : phi_dependency_index (E := positive) positive_encoding :=
  PhiDependencyIndex inputs audmp_dependency_graph
    (prepare positive_encoding audmp_dependency_graph)
    (GraphScc.SccResult [] [] CollectionsTrie.Trie.empty Map.empty) cycles.

Definition audmp_version_encode := audit_memory_version_encode audit_positive_encode
  audit_positive_encode.

Example audmp_cyclic_probe_retains_map :
  let index := audmp_index Map.empty (FinSet.of_list positive_encoding [1%positive]) in
  let run := audit_phi_resolve_step positive_encoding audit_positive_encode audmp_version_encode
    index Map.empty 1%positive in
  fst run = Map.empty /\ length (snd run) = 1.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_missing_row_probes_twice :
  let index := audmp_index Map.empty FinSet.empty in
  let run := audit_phi_resolve_step positive_encoding audit_positive_encode audmp_version_encode
    index Map.empty 1%positive in
  fst run = Map.empty /\ length (snd run) = 2.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_self_row_retains_map :
  let rows := Map.set positive_encoding 1%positive [(None, MemoryPhi 1%positive)] Map.empty in
  let run := audit_phi_resolve_step positive_encoding audit_positive_encode audmp_version_encode
    (audmp_index rows FinSet.empty) Map.empty 1%positive in
  fst run = Map.empty /\ length (snd run) = 7.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_equal_row_writes_representative :
  let rows := Map.set positive_encoding 1%positive [(None, @MemoryLive positive positive)]
    Map.empty in
  let run := audit_phi_resolve_step positive_encoding audit_positive_encode audmp_version_encode
    (audmp_index rows FinSet.empty) Map.empty 1%positive in
  Map.get (memory_version_encoding positive_encoding positive_encoding) (MemoryPhi 1%positive)
    (fst run) = Some MemoryLive /\ length (snd run) = 8.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_false_comparison_keeps_later_operand :
  let row := [(None, @MemoryLive positive positive);
    (Some 1%positive, MemoryPhi 2%positive); (Some 2%positive, MemoryLive)] in
  let rows := Map.set positive_encoding 1%positive row Map.empty in
  let run := audit_phi_resolve_step positive_encoding audit_positive_encode audmp_version_encode
    (audmp_index rows FinSet.empty) Map.empty 1%positive in
  fst run = Map.empty /\ length (snd run) = 17.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_pass_threads_first_write_into_second_read :
  let rows := Map.set positive_encoding 1%positive [(None, @MemoryLive positive positive)]
    (Map.set positive_encoding 2%positive [(None, MemoryPhi 1%positive)] Map.empty) in
  let run := audit_phi_resolve_all positive_encoding audit_positive_encode audmp_version_encode
    (audmp_index rows FinSet.empty) [1%positive; 2%positive] Map.empty in
  Map.get (memory_version_encoding positive_encoding positive_encoding) (MemoryPhi 2%positive)
    (fst run) = Some MemoryLive /\ length (snd run) = 16.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * Empty and nonempty complete fixed calls *)

Definition audmp_entry_graph : Graph.t unit unit :=
  {| Graph.entries := [tt];
     Graph.nodes := [tt];
     Graph.out := fun _ => [];
     Graph.source := fun _ => tt;
     Graph.target := fun _ => tt |}.

Definition audmp_effects (_ : unit) : list (memory_effect unit) := [].

Definition audmp_empty_memory : memory_graph unit unit :=
  MemoryGraph [] [MemoryLive] (fun _ => MemoryLive) (fun _ _ => None)
    (fun _ => MemoryLive) (fun _ _ => None).

Definition audmp_entry_memory : memory_graph unit unit :=
  MemoryGraph [tt] [MemoryLive; MemoryPhi tt] (fun _ => MemoryPhi tt)
    (fun _ _ => None) (fun _ => MemoryLive)
    (fun _ key =>
      match key with
      | None =>
        Some MemoryLive
      | Some _ =>
        None
      end).

Example audmp_empty_prune_retains_live :
  let run := audit_memory_phi_prune unit unit unit unit_encoding unit_encoding
    audmp_entry_graph audmp_effects audmp_empty_memory in
  memory_phis (phi_graph run) = [] /\ memory_versions (phi_graph run) = [MemoryLive].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_nonempty_prune_resolves_entry :
  let run := audit_memory_phi_prune unit unit unit unit_encoding unit_encoding
    audmp_entry_graph audmp_effects audmp_entry_memory in
  memory_phis (phi_graph run) = [] /\ memory_in (phi_graph run) tt = MemoryLive /\
    phi_rep unit_encoding unit_encoding run (MemoryPhi tt) = MemoryLive.
Proof.
  vm_compute; split; [reflexivity|split; reflexivity].
Qed.

Example audmp_complete_counted_prune_keeps_five_phases :
  let enc := fun _ : unit => (1%positive, [tt]) in
  let run := audit_memory_phi_prune_counted unit_encoding unit_encoding enc enc
    (fun _ => (@nil unit, [tt])) (fun _ => (tt, [tt]))
    (fun n key => (memory_operand audmp_entry_memory n key, [tt]))
    audmp_entry_graph audmp_effects audmp_entry_memory in
  let '(_, _, produced) := run in
  memory_phis (audit_phi_run_output unit_encoding produced) = [] /\
    length (audit_phi_run_preparation unit_encoding produced) = 5.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_complete_source_work_receipt :
  let enc := fun _ : unit => (1%positive, [tt]) in
  let run := audit_memory_phi_prune_counted unit_encoding unit_encoding enc enc
    (fun _ => (@nil unit, [tt])) (fun _ => (tt, [tt]))
    (fun n key => (memory_operand audmp_entry_memory n key, [tt]))
    audmp_entry_graph audmp_effects audmp_entry_memory in
  let '(_, preparation, produced) := run in
  N.of_nat (audit_prepare_source_work
    (audit_phi_input_graph_body_work (@length unit) (@length unit) (@length unit)) preparation +
    audit_phi_producer_work (@length unit) (@length unit)
      (audit_map_source_work (@length unit)) (@length unit)
      (audit_memory_version_work (@length unit) (@length unit)) unit_encoding produced) = 5252%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example audmp_complete_symbolic_input_budget node_charge edge_charge out_charge target_charge
    operand_charge :
  1 <= node_charge -> 1 <= edge_charge -> 1 <= out_charge -> 1 <= target_charge ->
  1 <= operand_charge ->
  let enc := fun _ : unit => (1%positive, [tt]) in
  let outgoing := fun _ : unit => (@nil unit, [tt]) in
  let target := fun _ : unit => (tt, [tt]) in
  let operand := fun n key => (memory_operand audmp_entry_memory n key, [tt]) in
  let '(base, preparation, produced) := audit_memory_phi_prune_counted unit_encoding unit_encoding
    enc enc outgoing target operand audmp_entry_graph audmp_effects audmp_entry_memory in
  audit_prepare_source_work
    (audit_phi_input_graph_body_work (@length unit) (@length unit) (@length unit)) preparation +
    audit_phi_producer_work (@length unit) (@length unit)
      (audit_map_source_work (@length unit)) (@length unit)
      (audit_memory_version_work (@length unit) (@length unit)) unit_encoding produced <=
  audit_prepare_source_budget unit_encoding audmp_entry_graph +
    audit_graph_prepare_full_event_bound audmp_entry_graph *
    audit_phi_input_graph_envelope outgoing target (fun _ => node_charge) (fun _ => out_charge)
      (fun _ => target_charge) (Graph.nodes audmp_entry_graph) +
    audit_phi_producer_input_budget unit_encoding unit_encoding enc enc
      (audit_phi_predecessors_counted unit_encoding enc audmp_entry_graph base) operand
      (fun _ => node_charge) (fun _ => edge_charge)
      (audit_phi_get_input_budget enc (fun _ => node_charge)) (fun _ _ => operand_charge)
      audmp_entry_graph audmp_effects audmp_entry_memory.
Proof.
  intros Hnode Hedge Hout Htarget Hoperand.
  apply audit_memory_phi_prune_whole_input_bound.
  - intros []; reflexivity.
  - intros []; reflexivity.
  - intros []; reflexivity.
  - intros []; exact Hnode.
  - intros []; exact Hedge.
  - intros []; exact Hout.
  - intros []; exact Htarget.
  - intros [] key; exact Hoperand.
Qed.

(** * Deferred field calls *)

Example audmp_missing_closure_retains_actual_callback_body :
  let base := fun _ : unit => (@None (memory_version positive positive), [tt; tt]) in
  let run := audit_phi_output_optional_call audmp_version_encode base Map.empty tt in
  fst run = None /\ snd run = [AuditPhiClosureCall tt None [tt; tt]].
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_present_closure_falls_back_on_missing_representative :
  let base := fun _ : unit => (Some (@MemoryPhi positive positive 3%positive), [tt]) in
  let run := audit_phi_output_optional_call audmp_version_encode base Map.empty tt in
  fst run = Some (MemoryPhi 3%positive) /\ length (snd run) = 2.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmp_singleton_cycle_scans_later_edge :
  let edges := [PhiDependencyEdgeData 1%positive (@None positive) 1%positive;
    PhiDependencyEdgeData 1%positive None 2%positive] in
  let dep := {| Graph.entries := [1%positive]; Graph.nodes := [1%positive];
    Graph.out := fun _ => edges; Graph.source := dependency_source;
    Graph.target := dependency_target |} in
  let run := audit_phi_cycle_self_edges audit_positive_encode dep 1%positive edges in
  fst run = true /\ length (snd run) = 11.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** * Actual proof-carrying public consumers *)

Lemma audmp_entry_cfg_wf : graph_wf audmp_entry_graph.
Proof.
  constructor.
  - constructor; [cbn; tauto|constructor].
  - intros [] _; cbn; tauto.
  - intros [] [] Hedge; contradiction.
  - intros [] [] _ Hedge; contradiction.
Qed.

Lemma audmp_entry_memory_wf :
  memory_graph_wf audmp_entry_graph audmp_effects audmp_entry_memory.
Proof.
  constructor.
  - exact audmp_entry_cfg_wf.
  - constructor; [cbn; tauto|constructor].
  - intros [] _; apply reachable_entry; cbn; tauto.
  - constructor; [cbn; intuition discriminate|].
    constructor; [cbn; tauto|constructor].
  - intros [|[]|[] i]; cbn.
    + tauto.
    + split.
      * intros _; split.
        -- apply reachable_entry; cbn; auto.
        -- unfold memory_phi_at; cbn; auto.
      * intros _; cbn; auto.
    + split.
      * intros [Hfalse|[Hfalse|Hfalse]]; [discriminate|discriminate|contradiction].
      * intros [a [[Hedge _] _]]; contradiction.
  - intros [] _; left; split; [unfold memory_phi_at; cbn; tauto|split; reflexivity].
  - intros [] Hedge; contradiction.
  - intros [] Hedge; contradiction.
  - intros [] _; split; [apply reachable_entry; cbn; tauto|unfold memory_phi_at; cbn; tauto].
  - intros [] Hedge; contradiction.
  - intros [] i; split.
    + intros [v Hlookup]; discriminate.
    + intros [a [Hedge _]]; contradiction.
  - intros [] [[]|]; unfold memory_phi_at; cbn.
    + split.
      * intros [v Hlookup]; discriminate.
      * intros [_ [Hedge _]]; contradiction.
    + split.
      * intros _; split; cbn; tauto.
      * intros _; exists MemoryLive; reflexivity.
Qed.

Example audmp_public_removed_operand_is_absent :
  let result := proj1_sig (memory_prune_with_map unit unit unit unit_encoding unit_encoding
    audmp_entry_graph audmp_effects audmp_entry_memory audmp_entry_memory_wf) in
  memory_phis (phi_graph result) = [] /\
  memory_operand (phi_graph result) tt None = None /\
  phi_rep unit_encoding unit_encoding result (MemoryPhi tt) = MemoryLive.
Proof.
  vm_compute; split; [reflexivity|split; reflexivity].
Qed.

Example audmp_public_output_wf :
  let output := proj1_sig (memory_prune unit unit unit unit_encoding unit_encoding
    audmp_entry_graph audmp_effects audmp_entry_memory audmp_entry_memory_wf) in
  memory_graph_wf audmp_entry_graph audmp_effects output.
Proof.
  apply proj2_sig.
Qed.

Example audmp_public_projection_consumer :
  proj1_sig (memory_prune unit unit unit unit_encoding unit_encoding
    audmp_entry_graph audmp_effects audmp_entry_memory audmp_entry_memory_wf) =
  phi_graph (proj1_sig (memory_prune_with_map unit unit unit unit_encoding unit_encoding
    audmp_entry_graph audmp_effects audmp_entry_memory audmp_entry_memory_wf)).
Proof.
  reflexivity.
Qed.

(** * Captured operand queries and strict callback receipts *)

Definition audmp_query_old : memory_graph positive positive :=
  MemoryGraph [1%positive; 2%positive] [MemoryLive; MemoryPhi 1%positive; MemoryPhi 2%positive]
    (fun _ => MemoryLive) (fun _ _ => None) (fun _ => MemoryLive)
    (fun n key => fst (audmp_operand n key)).

Definition audmp_query_reps :
    Map.t (memory_version positive positive) (memory_version positive positive) :=
  Map.set (memory_version_encoding positive_encoding positive_encoding)
    (MemoryPhi 2%positive) MemoryLive Map.empty.

Definition audmp_query_index :=
  audit_phi_operand_output_index positive_encoding positive_encoding audmp_query_old
    audmp_query_reps.

Definition audmp_query_base (input : positive * option positive) :=
  audmp_operand (fst input) (snd input).

Definition audmp_query_saved :=
  audit_phi_operand_saved_query audit_positive_encode audmp_version_encode audmp_query_index
    audmp_query_base audmp_query_reps.

Example audmp_guarded_empty_skips_operand_and_representative :
  let run := audit_phi_output_operand_call audit_positive_encode audmp_version_encode FinSet.empty
    audmp_query_base audmp_query_reps (1%positive, None) in
  fst run = None /\
  match snd run with
  | [AuditPhiOperandProbe _ false _; AuditPhiOperandAbsent] => True
  | _ => False
  end.
Proof.
  vm_compute; split; [reflexivity|exact I].
Qed.

Example audmp_guarded_repeated_hit_miss_and_missing_operand :
  map (fun input => fst (audmp_query_saved input))
    [(1%positive, None); (2%positive, None); (1%positive, Some 1%positive);
      (1%positive, Some 2%positive); (1%positive, None)] =
  [Some MemoryLive; None; None; Some MemoryLive; Some MemoryLive].
Proof.
  vm_compute; reflexivity.
Qed.

Example audmp_guarded_hit_records_actual_callback :
  match snd (audmp_query_saved (1%positive, Some 2%positive)) with
  | [AuditPhiOperandProbe _ true _;
      AuditPhiOperandBody [AuditPhiClosureCall _ (Some (MemoryPhi _)) [tt];
        AuditPhiClosureRead _ (Some MemoryLive) _]] => True
  | _ => False
  end.
Proof.
  vm_compute; exact I.
Qed.

Example audmp_guarded_miss_skips_actual_callback :
  match snd (audmp_query_saved (2%positive, None)) with
  | [AuditPhiOperandProbe _ false _; AuditPhiOperandAbsent] => True
  | _ => False
  end.
Proof.
  vm_compute; exact I.
Qed.

Example audmp_guarded_missing_operand_skips_representative :
  match snd (audmp_query_saved (1%positive, Some 1%positive)) with
  | [AuditPhiOperandProbe _ true _;
      AuditPhiOperandBody [AuditPhiClosureCall _ None [tt; tt]]] => True
  | _ => False
  end.
Proof.
  vm_compute; exact I.
Qed.

Example audmp_guarded_malformed_position_lookup :
  let malformed : FinSet.t positive := Trie.set 1%positive (7%positive, tt) Trie.empty in
  let run := audit_phi_output_operand_call audit_positive_encode audmp_version_encode malformed
    audmp_query_base audmp_query_reps (1%positive, None) in
  fst run = Some MemoryLive /\
  match snd run with
  | [AuditPhiOperandProbe _ true _; AuditPhiOperandBody _] => True
  | _ => False
  end.
Proof.
  vm_compute; split; [reflexivity|exact I].
Qed.

Example audmp_guarded_persistent_output_index :
  let kept := fst (audit_phi_output_keep_phis positive_encoding positive_encoding
    audit_positive_encode audmp_version_encode audmp_query_reps (memory_phis audmp_query_old)) in
  let '(captured, calls) := audit_finset_of_list audit_positive_encode kept in
  captured = audmp_query_index /\
  In (AuditSetFold [] captured) calls /\
  In (AuditPhiOutputSetBuild calls)
    (snd (audit_phi_producer_output_counted positive_encoding positive_encoding
      audit_positive_encode audmp_version_encode audmp_query_old audmp_query_reps)) /\
  fst (audmp_query_saved (1%positive, Some 2%positive)) =
    memory_operand (audit_phi_producer_output positive_encoding positive_encoding
      audmp_query_old audmp_query_reps) 1%positive (Some 2%positive).
Proof.
  vm_compute; intuition.
Qed.

Example audmp_guarded_source_work_receipts :
  let work := fun input => N.of_nat (audit_phi_operand_query_source_work audit_basic_encoding_work
    (audit_memory_version_work audit_basic_encoding_work audit_basic_encoding_work) (@length unit)
    (snd (audmp_query_saved input))) in
  work (1%positive, None) = 29%N /\
  work (2%positive, None) = 15%N /\
  work (1%positive, Some 1%positive) = 18%N /\
  work (1%positive, Some 2%positive) = 42%N /\
  fold_right (fun input total => (work input + total)%N) 0%N
    [(1%positive, None); (2%positive, None); (1%positive, Some 1%positive);
      (1%positive, Some 2%positive); (1%positive, None)] = 133%N.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
