(** * Concrete memo and saved snapshot examples

    These examples exercise persistent reuse, binary credit, malformed operands and saved snapshots.
    For example, two equal child occurrences share one terminal expansion and retain both probes.
    Builds on: concrete memo execution, public snapshot refresh and their adequacy proofs. *)

From Stdlib Require Import List NArith PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditMap CollectionsAuditFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare GraphAuditBase.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryWalk
  AnalysesAuditMemoryState AnalysesAuditMemoryStateAdequacy AnalysesAuditMemoryEncoding
  AnalysesAuditMemoryRawNext AnalysesAuditMemoryMemo AnalysesAuditMemoryMemoPlain
  AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryMemoExecuteAdequacy
  AnalysesAuditMemoryMemoExecuteBound AnalysesAuditMemoryMemoExecuteBoundAdequacy
  AnalysesAuditMemoryMemoPublicSource AnalysesAuditMemoryMemoPublicSourceAdequacy
  AnalysesAuditMemoryTable AnalysesAuditMemoryGraphCallbacks
  AnalysesAuditMemoryMemoSnapshot AnalysesAuditMemoryMemoSnapshotSource
  AnalysesAuditMemorySnapshotPublic AnalysesAuditMemorySnapshotPublicAdequacy.
Import List.ListNotations.

Definition audmw_version (v : memory_version unit unit) :=
  (encode (memory_version_encoding unit_encoding unit_encoding) v, [tt]).

Definition audmw_key (key : positive * memory_version unit unit) :=
  (encode (memo_key unit_encoding unit_encoding) key, [tt]).

Definition audmw_next (v : memory_version unit unit) : list (memory_version unit unit) * list unit
  :=
  match v with
  | MemoryPhi _ => ([MemoryLive; MemoryLive], [tt])
  | _ => ([], [tt])
  end.

Fixpoint audmw_expansions {N E CV CK NE} (events : list (audit_memo_event N E CV CK NE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoExpand _ _ _ :: rest => S (audmw_expansions rest)
  | _ :: rest => audmw_expansions rest
  end.

Example audmw_binary_borrow :
  audit_memo_pred 8%N =
    (7%N, [AuditMemoCreditCase 8%N; AuditMemoPredPositiveCase 8%positive;
      AuditMemoPredDoubleCase 4%positive; AuditMemoPredDoubleCase 2%positive;
      AuditMemoPredDoubleCase 1%positive]).
Proof.
  reflexivity.
Qed.

Example audmw_empty_union :
  fst (audit_memo_union audmw_version [] []) = [] /\
  length (fst (snd (audit_memo_union audmw_version [] []))) = 1.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmw_zero_credit :
  let run := audit_memo_execute audmw_version audmw_key 1%positive audmw_next
    0%N FinSet.empty Map.empty (MemoryPhi tt) in
  audit_memo_value run = MemoryClobberResult [MemoryPhi tt] false /\
  audit_memo_credit run = 0%N /\ audmw_expansions (audit_memo_body_events run) = 0.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example audmw_terminal_credit :
  let run := audit_memo_execute audmw_version audmw_key 1%positive audmw_next
    1%N FinSet.empty Map.empty MemoryLive in
  audit_memo_value run = MemoryClobberResult [MemoryLive] true /\
  audit_memo_credit run = 0%N /\ length (audit_memo_control_events run) = 3.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition audmw_saved_live : Map.t (positive * memory_version unit unit) (memo_entry unit unit) :=
  fst (audit_map_set audmw_key
  (1%positive, MemoryLive) (MemoDone [MemoryLive]) Map.empty).

Example audmw_done_preserves_credit :
  let run := audit_memo_execute audmw_version audmw_key 1%positive audmw_next
    8%N FinSet.empty audmw_saved_live MemoryLive in
  audit_memo_value run = MemoryClobberResult [MemoryLive] true /\
  audit_memo_cache run = audmw_saved_live /\ audit_memo_credit run = 8%N /\
  audit_memo_control_events run = [AuditMemoEnterCase].
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example audmw_duplicate_children_share_cache :
  let run := audit_memo_execute audmw_version audmw_key 1%positive audmw_next
    8%N FinSet.empty Map.empty (MemoryPhi tt) in
  audit_memo_value run = MemoryClobberResult [MemoryLive] true /\
  audit_memo_credit run = 6%N /\ audmw_expansions (audit_memo_body_events run) = 2 /\
  audit_memo_successor_occurrences (audit_memo_body_events run) = 2 /\
  Map.get (memo_key unit_encoding unit_encoding) (1%positive, MemoryLive)
    (audit_memo_cache run) = Some (MemoDone [MemoryLive]).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example audmw_exact_cutoff_boundary :
  let run := audit_memo_execute audmw_version audmw_key 1%positive audmw_next
    1%N FinSet.empty Map.empty (MemoryPhi tt) in
  audit_memo_value run = MemoryClobberResult [MemoryLive] false /\
  audit_memo_cache run = Map.empty /\ audit_memo_credit run = 0%N.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example audmw_active_priority :
  let active := audit_finset_add audmw_version (MemoryPhi tt) FinSet.empty in
  let run := audit_memo_execute audmw_version audmw_key 1%positive audmw_next
    8%N (fst active) Map.empty (MemoryPhi tt) in
  audit_memo_value run = MemoryClobberResult [MemoryPhi tt] false /\
  audit_memo_credit run = 8%N /\ length (audit_memo_body_events run) = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example audmw_busy_cut :
  let memo := fst (audit_map_set audmw_key (1%positive, MemoryPhi tt) MemoBusy Map.empty) in
  let run := audit_memo_execute audmw_version audmw_key 1%positive audmw_next
    8%N FinSet.empty memo (MemoryPhi tt) in
  audit_memo_value run = MemoryClobberResult [MemoryPhi tt] false /\
  audit_memo_cache run = memo /\ audit_memo_credit run = 8%N.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example audmw_scope_mismatch_expands :
  let memo := fst (audit_map_set audmw_key (2%positive, MemoryPhi tt)
    (MemoDone [MemoryDef tt 0]) Map.empty) in
  let run := audit_memo_execute audmw_version audmw_key 1%positive audmw_next
    8%N FinSet.empty memo (MemoryPhi tt) in
  audit_memo_value run = MemoryClobberResult [MemoryLive] true /\
  audmw_expansions (audit_memo_body_events run) = 2.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition audmw_unit (value : unit) := (encode unit_encoding value, [tt]).

Definition audmw_incoming (_ : unit) := ([tt; tt], [tt]).

Definition audmw_operand (_ : unit) (key : option unit) :=
  let value :=
    match key with
    | None => None
    | Some _ => Some (@MemoryLive unit unit)
    end in
  (value, [tt]).

Definition audmw_before (_ : unit) (_ : nat) := (Some (@MemoryLive unit unit), [tt]).

Example audmw_missing_and_duplicate_operands :
  let result := audit_memory_raw_next audmw_unit audmw_unit Map.empty audmw_incoming
    audmw_operand audmw_before MemoryAll (MemoryPhi tt) in
  fst result = [MemoryLive; MemoryLive] /\ length (snd result) = 5.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmw_missing_effect_skips_before :
  let result := audit_memory_raw_next audmw_unit audmw_unit Map.empty audmw_incoming
    audmw_operand audmw_before MemoryAll (MemoryDef tt 0) in
  fst result = [] /\ length (snd result) = 2.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition audit_invalid_phi_graph : Graph.t unit unit :=
  Graph.Make [] [tt] (fun _ => []) (fun _ => tt) (fun _ => tt).

Definition audit_invalid_phi_memory : memory_graph unit unit :=
  MemoryGraph [] [MemoryLive] (fun _ => MemoryLive) (fun _ _ => None)
    (fun _ => MemoryLive) (fun _ _ => None).

Definition audit_invalid_phi_effects (_ : unit) : list (memory_effect unit) := [].

Definition audit_invalid_phi_initial := AnalysesAuditMemoryState.memo_initial unit_encoding
  unit_encoding audit_invalid_phi_graph audit_invalid_phi_effects audit_invalid_phi_memory.

Definition audit_invalid_phi_query := audit_memory_memo_query unit_encoding unit_encoding
  unit_encoding
  audit_invalid_phi_graph audit_invalid_phi_effects audit_invalid_phi_memory
    audit_invalid_phi_initial
  MemoryAll (MemoryPhi tt) 1%positive.

Example audit_invalid_phi_cached_done :
  Map.get (memo_key unit_encoding unit_encoding) (scope_code unit_encoding MemoryAll, MemoryPhi tt)
    (@memo_entries unit unit unit unit_encoding audit_invalid_phi_graph audit_invalid_phi_effects
      audit_invalid_phi_memory (snd audit_invalid_phi_query)) = Some (MemoDone [MemoryPhi tt]).
Proof.
  vm_compute; reflexivity.
Qed.

Example audit_invalid_phi_not_valid :
  ~ memory_valid_version audit_invalid_phi_graph audit_invalid_phi_effects audit_invalid_phi_memory
    (MemoryPhi tt).
Proof.
  intros [Hreachable Hphi]; exact Hphi.
Qed.

Example audit_invalid_phi_initial_valid :
  memo_valid unit_encoding unit_encoding unit_encoding audit_invalid_phi_graph
    audit_invalid_phi_effects audit_invalid_phi_memory audit_invalid_phi_initial.
Proof.
  apply AnalysesAuditMemoryStateAdequacy.memo_initial.
Qed.

Example audit_invalid_phi_query_not_valid :
  ~ memo_valid unit_encoding unit_encoding unit_encoding audit_invalid_phi_graph
    audit_invalid_phi_effects audit_invalid_phi_memory (snd audit_invalid_phi_query).
Proof.
  intros [Hadj [Htable [Hwf [Hbusy Hdone]]]].
  destruct (Hdone MemoryAll (MemoryPhi tt) [MemoryPhi tt] audit_invalid_phi_cached_done)
    as [Hroots [Hstart Hresult]].
  exact (audit_invalid_phi_not_valid Hstart).
Qed.

Definition audmw_saved_snapshot := @MemoSnapshot unit unit unit positive 1%positive
  audit_invalid_phi_graph audit_invalid_phi_effects audit_invalid_phi_memory.

Definition audmw_saved_cache := @AuditSnapshotMemoCache unit unit unit positive unit_encoding
  audmw_saved_snapshot (prepare unit_encoding audit_invalid_phi_graph)
  (memory_walk_effect_table unit_encoding audit_invalid_phi_graph audit_invalid_phi_effects)
  (@memo_entries unit unit unit unit_encoding audit_invalid_phi_graph audit_invalid_phi_effects
    audit_invalid_phi_memory (snd (audit_memory_memo_query unit_encoding unit_encoding unit_encoding
      audit_invalid_phi_graph audit_invalid_phi_effects audit_invalid_phi_memory
      audit_invalid_phi_initial MemoryAll MemoryLive 1%positive))).

Definition audmw_current_graph : Graph.t unit unit :=
  Graph.Make [tt] [tt] (fun _ => []) (fun _ => tt) (fun _ => tt).

Definition audmw_current_memory : memory_graph unit unit :=
  MemoryGraph [tt] [MemoryLive; MemoryPhi tt] (fun _ => MemoryPhi tt) (fun _ _ => None)
    (fun _ => MemoryLive) (fun _ _ => Some MemoryLive).

Definition audmw_current_snapshot epoch := @MemoSnapshot unit unit unit positive epoch
  audmw_current_graph audit_invalid_phi_effects audmw_current_memory.

Example audmw_epoch_hit_preserves_nonempty_saved_cache :
  audit_snapshot_refresh_compute unit_encoding unit_encoding positive_encoding audmw_saved_cache
    (audmw_current_snapshot 1%positive) = audmw_saved_cache /\
  Map.get (memo_key unit_encoding unit_encoding) (scope_code unit_encoding MemoryAll, MemoryLive)
    (audit_cache_entries audmw_saved_cache) = Some (MemoDone [MemoryLive]).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmw_epoch_miss_rebuilds_current :
  let fresh := audit_snapshot_refresh_compute unit_encoding unit_encoding positive_encoding
    audmw_saved_cache (audmw_current_snapshot 2%positive) in
  audit_cache_snapshot fresh = audmw_current_snapshot 2%positive /\
  audit_cache_entries fresh = Map.empty /\
  audit_cache_prepared fresh = prepare unit_encoding audmw_current_graph.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example audmw_saved_query_uses_saved_operands :
  let reused := audit_snapshot_refresh_compute unit_encoding unit_encoding positive_encoding
    audmw_saved_cache (audmw_current_snapshot 1%positive) in
  fst (audit_snapshot_query unit_encoding unit_encoding unit_encoding reused MemoryAll
    (MemoryPhi tt) 2%positive) = MemoryClobberResult [MemoryPhi tt] true /\
  fst (audit_memory_memo_query unit_encoding unit_encoding unit_encoding audmw_current_graph
    audit_invalid_phi_effects audmw_current_memory
    (AnalysesAuditMemoryState.memo_initial unit_encoding unit_encoding audmw_current_graph
      audit_invalid_phi_effects audmw_current_memory) MemoryAll (MemoryPhi tt) 2%positive) =
    MemoryClobberResult [MemoryLive] true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmw_incompatible_epoch_domain_rejected :
  ~ memo_epoch_laws (fun snapshot => snapshot = audmw_saved_snapshot \/
    snapshot = audmw_current_snapshot 1%positive).
Proof.
  intro Hlaws.
  destruct (epoch_equal_observations _ Hlaws audmw_saved_snapshot (audmw_current_snapshot
    1%positive)
    (or_introl eq_refl) (or_intror eq_refl) eq_refl) as [[Hentries Hgraph] Hmemory].
  discriminate Hentries.
Qed.

Example audmw_saved_memory_well_formed :
  memory_graph_wf audit_invalid_phi_graph audit_invalid_phi_effects audit_invalid_phi_memory.
Proof.
  constructor.
  - constructor.
    + constructor; [cbn; tauto|constructor].
    + intros node Hentry; cbn in Hentry; contradiction.
    + intros node edge Hedge; cbn in Hedge; contradiction.
    + intros node edge Hnode Hedge; cbn in Hedge; contradiction.
  - constructor.
  - intros node Hphi; cbn [memory_phi_at audit_invalid_phi_memory] in Hphi; contradiction.
  - constructor; [cbn; tauto|constructor].
  - intros [|node|edge index]; cbn [memory_valid_version memory_phi_at memory_occurrence].
    + cbn; tauto.
    + cbn; intuition discriminate.
    + cbn; split.
      * intros [Hsame|Hfalse]; [discriminate|contradiction].
      * intros [effect [[Hedge Hrest] Hdef]]; cbn in Hedge; contradiction.
  - intros node Hentry; cbn in Hentry; contradiction.
  - intros edge Hedge Hreachable; cbn in Hedge; contradiction.
  - intros edge Hedge Hreachable; cbn in Hedge; contradiction.
  - intros node Hreachable; exact I.
  - intros edge Hedge Hreachable; exact I.
  - intros edge index; cbn [memory_occurrence]; split.
    + intros [version Hlookup]; discriminate Hlookup.
    + intros [effect [Hedge Hrest]]; cbn in Hedge; contradiction.
  - intros node key; cbn [memory_phi_at]; split.
    + intros [version Hlookup]; discriminate Hlookup.
    + intros [Hphi Hrest]; cbn in Hphi; contradiction.
Qed.

Example audmw_saved_full_semantic_validity :
  audit_snapshot_semantic_valid unit_encoding unit_encoding unit_encoding audmw_saved_cache.
Proof.
  exact (proj1 (audit_memory_memo_query_correct unit unit unit unit_encoding unit_encoding
    unit_encoding audit_invalid_phi_graph audit_invalid_phi_effects audit_invalid_phi_memory
    audit_invalid_phi_initial MemoryAll MemoryLive 1%positive audit_invalid_phi_initial_valid
    audmw_saved_memory_well_formed I)).
Qed.

Definition audmw_equivalent_graph : Graph.t unit unit :=
  Graph.Make [] [tt]
    (fun node =>
      match node with
      | tt => []
      end) (fun _ => tt) (fun _ => tt).

Definition audmw_equivalent_snapshot := @MemoSnapshot unit unit unit positive 1%positive
  audmw_equivalent_graph audit_invalid_phi_effects audit_invalid_phi_memory.

Definition audmw_equivalent_domain snapshot : Prop :=
  snapshot = audmw_saved_snapshot \/ snapshot = audmw_equivalent_snapshot.

Example audmw_equivalent_epoch_laws : memo_epoch_laws audmw_equivalent_domain.
Proof.
  constructor; intros old current Hold Hcurrent Hepoch.
  destruct Hold as [-> | ->]; destruct Hcurrent as [-> | ->];
    unfold graph_observations_equal, memory_observations_equal;
    repeat split; try reflexivity; intros []; repeat split; reflexivity.
Qed.

Example audmw_current_complete_uses_pointwise_observations :
  forall version,
    In version (clobber_roots (fst (audit_snapshot_query unit_encoding unit_encoding unit_encoding
      audmw_saved_cache MemoryAll MemoryLive 2%positive))) <->
    memory_walk_terminal unit_encoding audit_invalid_phi_effects audit_invalid_phi_memory MemoryAll
      version /\ exists trace,
      memory_walk_trace unit_encoding audit_invalid_phi_effects audit_invalid_phi_memory MemoryAll
        MemoryLive trace /\ memory_trace_last trace = Some version.
Proof.
  apply (audit_snapshot_query_current_complete unit unit unit positive unit_encoding unit_encoding
    unit_encoding positive_encoding audmw_equivalent_domain audmw_saved_cache
    audmw_equivalent_snapshot MemoryAll MemoryLive 2%positive audmw_equivalent_epoch_laws
    (or_introl eq_refl) (or_intror eq_refl) eq_refl audmw_saved_full_semantic_validity).
  - apply (audit_snapshot_memory_wf_transport unit unit unit audit_invalid_phi_graph
      audmw_equivalent_graph audit_invalid_phi_effects audit_invalid_phi_effects
      audit_invalid_phi_memory audit_invalid_phi_memory).
    + repeat split; try reflexivity; intros []; repeat split; reflexivity.
    + intro edge; reflexivity.
    + repeat split; intros; reflexivity.
    + exact audmw_saved_memory_well_formed.
  - exact I.
  - vm_compute; reflexivity.
Qed.

Definition audmw_full_graph : Graph.t unit unit :=
  Graph.Make [tt] [tt] (fun _ => [tt; tt]) (fun _ => tt) (fun _ => tt).

Definition audmw_full_out (_ : unit) := ([tt; tt], [tt]).

Definition audmw_full_target (_ : unit) := (tt, [tt]).

Definition audmw_full_effects (_ : unit) :=
  ([MemoryRead (@MemoryRegions unit []); MemoryWrite (MemoryRegions [Footprint tt 0%Z 1%Z])], [tt]).

Definition audmw_full_operand (_ : unit) (_ : option unit) :=
  (Some (@MemoryLive unit unit), [tt]).

Definition audmw_full_before (_ : unit) (_ : nat) :=
  (@None (memory_version unit unit), [tt]).

Definition audmw_full_setup := audit_memory_memo_initial_source_counted unit_encoding audmw_unit
  audmw_unit audmw_full_out audmw_full_target audmw_full_effects audmw_full_graph
    audmw_current_memory.

Definition audmw_full_query := audit_memory_memo_public_source_counted audmw_unit audmw_unit
  audmw_unit unit_encoding audmw_full_graph (fun edge => fst (audmw_full_effects edge))
  audmw_current_memory (fst audmw_full_setup) audmw_full_operand audmw_full_before
  (MemoryRegions [Footprint tt 0%Z 1%Z]) (MemoryPhi tt) 8%positive.

Definition audmw_full_setup_work : nat :=
  4 + audit_prepare_source_work (audit_snapshot_graph_body_work (@length unit) (@length unit)
    (@length unit)) (fst (snd audmw_full_setup)) +
    audit_memory_table_work (@length unit) (@length unit) (@length unit) (snd (snd
      audmw_full_setup)).

Definition audmw_full_query_work : nat :=
  4 + audit_memory_scope_work (@length unit) (snd (fst audmw_full_query)) +
    audit_memo_execution_source_work (audit_memory_version_work (@length unit) (@length unit))
      (audit_memory_memo_key_work (@length unit) (@length unit))
      (audit_raw_next_source_work (@length unit) (@length unit)
        (audit_map_source_work (@length unit)) (@length unit) (@length unit)) (snd
          audmw_full_query).

Example audmw_full_source_retains_occurrences :
  audit_memo_value (snd audmw_full_query) = MemoryClobberResult [MemoryLive] true /\
  audit_memo_credit (snd audmw_full_query) = 6%N /\
  audit_memo_successor_occurrences (audit_memo_body_events (snd audmw_full_query)) = 3 /\
  audmw_expansions (audit_memo_body_events (snd audmw_full_query)) = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Example audmw_full_setup_binary_work_bound :
  (0 <? N.of_nat audmw_full_setup_work)%N = true /\
  (N.of_nat audmw_full_setup_work <=? 100000)%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmw_full_query_binary_work_bound :
  (0 <? N.of_nat audmw_full_query_work)%N = true /\
  (N.of_nat audmw_full_query_work <=? 100000)%N = true.
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmw_full_public_erases :
  let plain := audit_memory_memo_query unit_encoding unit_encoding unit_encoding audmw_full_graph
    (fun edge => fst (audmw_full_effects edge)) audmw_current_memory (fst audmw_full_setup)
    (MemoryRegions [Footprint tt 0%Z 1%Z]) (MemoryPhi tt) 8%positive in
  audit_memo_value (snd audmw_full_query) = fst plain /\
  audit_memo_cache (snd audmw_full_query) =
    @memo_entries unit unit unit unit_encoding audmw_full_graph
      (fun edge => fst (audmw_full_effects edge)) audmw_current_memory (snd plain).
Proof.
  apply audit_memory_memo_public_source_erases; intros; reflexivity.
Qed.

Definition audmw_valid_phi_memory : memory_graph unit unit :=
  MemoryGraph [tt] [MemoryLive; MemoryPhi tt] (fun _ => MemoryPhi tt) (fun _ _ => None)
    (fun _ => MemoryLive)
    (fun _ key =>
      match key with
      | None => Some MemoryLive
      | Some _ => None
      end).

Example audmw_valid_phi_memory_well_formed :
  memory_graph_wf audmw_current_graph audit_invalid_phi_effects audmw_valid_phi_memory.
Proof.
  constructor.
  - constructor.
    + constructor; [cbn; tauto|constructor].
    + intros node Hentry; exact Hentry.
    + intros node edge Hedge; cbn in Hedge; contradiction.
    + intros node edge Hnode Hedge; cbn in Hedge; contradiction.
  - constructor; [cbn; tauto|constructor].
  - intros [] Hphi; constructor; left; reflexivity.
  - constructor; [cbn; intuition discriminate|constructor; [cbn; tauto|constructor]].
  - intros [|[]|edge index]; cbn [memory_valid_version memory_phi_at memory_occurrence].
    + cbn; intuition discriminate.
    + split.
      * intro Hin; split; [constructor; left; reflexivity|left; reflexivity].
      * intro Hvalid; right; left; reflexivity.
    + cbn; split.
      * intros [Hsame|[Hsame|Hfalse]]; try discriminate; contradiction.
      * intros [effect [[Hedge Hrest] Hdef]]; cbn in Hedge; contradiction.
  - intros [] Hentry; left; split; [left; reflexivity|split; reflexivity].
  - intros edge Hedge Hreachable; cbn in Hedge; contradiction.
  - intros edge Hedge Hreachable; cbn in Hedge; contradiction.
  - intros [] Hreachable; split; [exact Hreachable|left; reflexivity].
  - intros edge Hedge Hreachable; exact I.
  - intros edge index; cbn [memory_occurrence]; split.
    + intros [version Hlookup]; discriminate Hlookup.
    + intros [effect [Hedge Hrest]]; cbn in Hedge; contradiction.
  - intros [] [edge|]; cbn [memory_phi_at]; split.
    + intros [version Hlookup]; discriminate Hlookup.
    + intros [Hphi [Hedge Hrest]]; cbn in Hedge; contradiction.
    + intro Hsome; split; left; reflexivity.
    + intro Hdomain; exists MemoryLive; reflexivity.
Qed.

Definition audmw_valid_phi_initial := AnalysesAuditMemoryState.memo_initial unit_encoding
  unit_encoding audmw_current_graph audit_invalid_phi_effects audmw_valid_phi_memory.

Definition audmw_valid_phi_query := audit_memory_memo_query unit_encoding unit_encoding
  unit_encoding
  audmw_current_graph audit_invalid_phi_effects audmw_valid_phi_memory audmw_valid_phi_initial
  MemoryAll (MemoryPhi tt) 2%positive.

Example audmw_valid_phi_completes_and_stores :
  fst audmw_valid_phi_query = MemoryClobberResult [MemoryLive] true /\
  Map.get (memo_key unit_encoding unit_encoding) (scope_code unit_encoding MemoryAll, MemoryPhi tt)
    (@memo_entries unit unit unit unit_encoding audmw_current_graph audit_invalid_phi_effects
      audmw_valid_phi_memory (snd audmw_valid_phi_query)) = Some (MemoDone [MemoryLive]).
Proof.
  vm_compute; split; reflexivity.
Qed.

Example audmw_valid_phi_preserves_full_semantics :
  memo_valid unit_encoding unit_encoding unit_encoding audmw_current_graph audit_invalid_phi_effects
    audmw_valid_phi_memory (snd audmw_valid_phi_query).
Proof.
  assert (Hinitial : memo_valid unit_encoding unit_encoding unit_encoding audmw_current_graph
    audit_invalid_phi_effects audmw_valid_phi_memory audmw_valid_phi_initial).
  { apply AnalysesAuditMemoryStateAdequacy.memo_initial. }
  assert (Hstart : memory_valid_version audmw_current_graph audit_invalid_phi_effects
    audmw_valid_phi_memory (MemoryPhi tt)).
  { split; [constructor; left; reflexivity|left; reflexivity]. }
  exact (proj1 (audit_memory_memo_query_correct unit unit unit unit_encoding unit_encoding
    unit_encoding
    audmw_current_graph audit_invalid_phi_effects audmw_valid_phi_memory audmw_valid_phi_initial
    MemoryAll (MemoryPhi tt) 2%positive Hinitial audmw_valid_phi_memory_well_formed Hstart)).
Qed.

Example audmw_second_public_query_reuses_returned_cache :
  audit_memory_memo_query unit_encoding unit_encoding unit_encoding audmw_current_graph
    audit_invalid_phi_effects audmw_valid_phi_memory (snd audmw_valid_phi_query)
    MemoryAll (MemoryPhi tt) 1%positive = audmw_valid_phi_query.
Proof.
  vm_compute; reflexivity.
Qed.

(** Inspect the captured expansion bodies without invoking any callback again. *)
Definition audmw_expanded_calls {N E CV CK NE}
    (events : list (audit_memo_event N E CV CK NE)) :=
  flat_map
    (fun event =>
      match event with
      | AuditMemoExpand version successors calls => [(version, successors, calls)]
      | _ => []
      end) events.

Definition audmw_unvisited_phi_run := snd (audit_memory_memo_public_source_counted audmw_unit
  audmw_unit audmw_unit unit_encoding audmw_current_graph audit_invalid_phi_effects
  audmw_valid_phi_memory audmw_valid_phi_initial
  (fun node key => (memory_operand audmw_valid_phi_memory node key, [tt])) audmw_full_before
  MemoryAll MemoryLive 1%positive).

(** The inventory Phi remains unvisited: the only expansion contains the Live branch alone,
    with no incoming lookup or operand call. *)
Example audmw_inventory_phi_unvisited_raw_trace :
  memory_versions audmw_valid_phi_memory = [MemoryLive; MemoryPhi tt] /\
  audit_memo_value audmw_unvisited_phi_run = MemoryClobberResult [MemoryLive] true /\
  audmw_expanded_calls (audit_memo_body_events audmw_unvisited_phi_run) =
    [(MemoryLive, [], [AuditRawBranch MemoryLive])] /\
  audit_memo_credit audmw_unvisited_phi_run = 0%N.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

Definition audmw_unlisted_phi_run := snd (audit_memory_memo_public_source_counted audmw_unit
  audmw_unit audmw_unit unit_encoding audit_invalid_phi_graph audit_invalid_phi_effects
  audit_invalid_phi_memory audit_invalid_phi_initial
  (fun node key => (memory_operand audit_invalid_phi_memory node key, [tt])) audmw_full_before
  MemoryAll (MemoryPhi tt) 1%positive).

(** An unlisted Phi still expands. Its saved incoming trie is empty, so the exact raw body
    records one operand at node tt with key None, result None and retained body [tt]. *)
Example audmw_unlisted_phi_captured_raw_trace :
  memory_versions audit_invalid_phi_memory = [MemoryLive] /\
  audit_memo_value audmw_unlisted_phi_run = MemoryClobberResult [MemoryPhi tt] true /\
  audmw_expanded_calls (audit_memo_body_events audmw_unlisted_phi_run) =
    [(MemoryPhi tt, [],
      [AuditRawBranch (MemoryPhi tt);
        AuditRawIncoming tt []
          [AuditMapGet tt 1%positive Map.empty None [tt]
            [CollectionsAuditCost.AuditCall
              (CollectionsAuditTrie.AuditTrieKey 1%positive CollectionsTrie.Trie.Empty);
              CollectionsAuditCost.AuditCall
                (CollectionsAuditTrie.AuditTrieValue CollectionsTrie.Trie.Empty None)]];
        AuditRawOperand tt None None [tt]])] /\
  audit_memo_credit audmw_unlisted_phi_run = 0%N /\
  Map.get (memo_key unit_encoding unit_encoding)
    (scope_code unit_encoding MemoryAll, MemoryPhi tt)
    (audit_memo_cache audmw_unlisted_phi_run) = Some (MemoDone [MemoryPhi tt]).
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
