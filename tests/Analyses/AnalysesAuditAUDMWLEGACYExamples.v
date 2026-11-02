(** * Legacy and memo producer regression clients

    These clients retain the original publication fixtures and observe strict callback order,
    indexed answers and the persistent memo. For example, two retained loads share one expansion.
    Builds on: the six legacy adequacy leaves and their published source models. *)

From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCallback CollectionsAuditMap.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryWalk AnalysesMemoryLegacy
  AnalysesAuditMemoryLegacyChecker AnalysesAuditMemoryLegacyProjectionSource
  AnalysesAuditMemoryState AnalysesAuditMemoryEncoding AnalysesAuditMemoryMemo
  AnalysesAuditMemoryMemoExecute AnalysesAuditMemoryLegacyProposalSource
  AnalysesAuditMemoryLegacySetupSource AnalysesAuditMemoryMemoLegacyPlain
  AnalysesAuditMemoryMemoLegacySource AnalysesAuditMemoryLegacyBytesAdequacy
  AnalysesAuditMemoryLegacyProjectionSourceAdequacy AnalysesAuditMemoryLegacyProposalSourceAdequacy
  AnalysesAuditMemoryLegacySetupSourceAdequacy AnalysesAuditMemoryMemoLegacyPlainAdequacy
  AnalysesAuditMemoryMemoLegacySourceAdequacy.
Import List.ListNotations.

Definition audit_whole_graph : Graph.t bool unit :=
  Graph.Make [false] [false; true] (fun node => if node then [] else [tt])
    (fun _ => false) (fun _ => true).

Definition audit_whole_node (node : bool) := (encode bool_encoding node, [tt]).

Definition audit_whole_edge (_ : unit) := (encode unit_encoding tt, [tt]).

Definition audit_whole_effects (_ : unit) := ([@MemoryRead unit (MemoryRegions [])], [tt]).

Definition audit_whole_out (node : bool) := (Graph.out audit_whole_graph node, [tt]).

Definition audit_whole_target (_ : unit) := (true, [tt]).

Definition audit_whole_source (_ : unit) := (false, [tt]).

Definition audit_whole_operand (_ : bool) (_ : option unit) :=
  (Some (@MemoryLive bool unit), [tt]).

Definition audit_whole_before (_ : unit) (_ : nat) := (Some (@MemoryLive bool unit), [tt]).

Definition audit_whole_regions (_ : bool) : list (footprint unit) * list unit := ([], [tt]).

Definition audit_whole_load (node : bool) := (if node then None else Some (tt, 0), [tt]).

Definition audit_whole_memory : memory_graph bool unit :=
  MemoryGraph [true] [MemoryLive; MemoryPhi true] (fun _ => MemoryLive)
    (fun _ _ => Some MemoryLive) (fun _ => MemoryLive) (fun _ _ => Some MemoryLive).

(** A false load still pays the complete strict selected definition branch. *)

Example audit_whole_false_load_keeps_six_frames :
  fst audit_legacy_false_load_pair_fixture = false /\
  length (snd audit_legacy_false_load_pair_fixture) = 6.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** A false owner still pays reads, successor enumeration and the complete slice. *)

Example audit_whole_false_owner_keeps_six_frames :
  fst audit_legacy_false_owner_pair_fixture = false /\
  length (snd audit_legacy_false_owner_pair_fixture) = 6.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

Definition audit_whole_legacy_pipeline :=
  audit_legacy_projection_check_source_counted bool_encoding bool_encoding unit_encoding
    audit_whole_node audit_whole_edge audit_whole_node audit_whole_edge audit_whole_source
    audit_whole_out audit_whole_target audit_whole_effects audit_whole_operand audit_whole_before
    audit_whole_load audit_whole_regions audit_whole_regions audit_whole_graph audit_whole_memory
    false 2%positive.

(** The full producer closure and independent outer checker accept the nonempty graph. *)

Example audit_whole_legacy_pipeline_accepts :
  let '(accepted, _, _) := audit_whole_legacy_pipeline in accepted = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition audit_whole_def_effects (_ : unit) :=
  ([@MemoryWrite unit MemoryAll; MemoryRead (MemoryRegions [])], [tt]).

Definition audit_whole_def_before (_ : unit) (index : nat) :=
  (Some (match index with
    | 0 => @MemoryLive bool unit
    | _ => MemoryDef tt 0
    end), [tt]).

Definition audit_whole_def_load (node : bool) :=
  (if node then None else Some (tt, 1), [tt]).

Definition audit_whole_def_memory : memory_graph bool unit :=
  MemoryGraph [] [MemoryLive; MemoryDef tt 0] (fun _ => MemoryLive)
    (fun _ index => Some (match index with
      | 0 => MemoryLive
      | _ => MemoryDef tt 0
      end))
    (fun _ => MemoryDef tt 0) (fun _ _ => None).

Definition audit_whole_def_producer :=
  audit_legacy_projection_source_counted bool_encoding bool_encoding unit_encoding
    audit_whole_node audit_whole_edge audit_whole_node audit_whole_edge audit_whole_source
    audit_whole_out audit_whole_target audit_whole_def_effects audit_whole_operand
    audit_whole_def_before audit_whole_def_load audit_whole_regions audit_whole_regions
    audit_whole_graph audit_whole_def_memory false 2%positive.

(** The singleton definition result evaluates the actual source callback and survives retain. *)

Example audit_whole_singleton_definition_retained :
  let '(_, definitions) := audit_whole_def_producer in
  fst (definitions false) = Some (MDef false false).
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition audit_memo_legacy_fixture_graph : Graph.t bool bool :=
  Graph.Make [false] [false; true] (fun node => [node]) (fun edge => edge) (fun _ => true).

Definition audit_memo_legacy_fixture_memory : memory_graph bool bool :=
  MemoryGraph [] [MemoryLive] (fun _ => MemoryLive) (fun _ _ => Some MemoryLive)
    (fun _ => MemoryLive) (fun _ _ => None).

Definition audit_memo_legacy_fixture_effects (_ : bool) : list (memory_effect unit) :=
  [MemoryRead (MemoryRegions [])].

Definition audit_memo_legacy_fixture_state := memo_initial bool_encoding bool_encoding
  audit_memo_legacy_fixture_graph audit_memo_legacy_fixture_effects
    audit_memo_legacy_fixture_memory.

Definition audit_memo_legacy_fixture_plain := audit_memory_memo_legacy_project
  bool_encoding bool_encoding bool_encoding unit_encoding false audit_memo_legacy_fixture_graph
  audit_memo_legacy_fixture_effects (fun _ => []) (fun _ => []) audit_memo_legacy_fixture_memory
  audit_memo_legacy_fixture_state (fun node => Some (node, 0)) 1%positive.

Definition audit_memo_legacy_fixture_counted :=
  audit_memory_memo_legacy_project_counted bool_encoding bool_encoding unit_encoding
    audit_whole_node audit_whole_node audit_whole_node audit_whole_edge
    (fun edge => (edge, [tt])) (fun node => ([node], [tt])) (fun _ => (true, [tt]))
    (fun _ _ => (@None (memory_version bool bool), [tt]))
    (fun _ _ => (Some (@MemoryLive bool bool), [tt]))
    (fun node => (Some (node, 0), [tt])) (fun _ => ([], [tt])) (fun _ => ([], [tt]))
    audit_memo_legacy_fixture_graph audit_memo_legacy_fixture_effects
      audit_memo_legacy_fixture_memory
    false 1%positive audit_memo_legacy_fixture_state.

Fixpoint audit_fixture_memo_expands {N E CV CK NE}
    (events : list (audit_memo_event N E CV CK NE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoExpand _ _ _ :: rest => S (audit_fixture_memo_expands rest)
  | _ :: rest => audit_fixture_memo_expands rest
  end.

Fixpoint audit_fixture_memo_proposal_expands {F N E T CN CE SE XE OE BE LE RE}
    (events : list (audit_memo_legacy_proposal_event F N E T CN CE SE XE OE BE LE RE)) : nat :=
  match events with
  | [] => 0
  | AuditLegacySourceClobbers _ receipt :: rest =>
      audit_fixture_memo_expands (audit_memo_body_events (audit_memo_legacy_execution receipt)) +
      audit_fixture_memo_proposal_expands rest
  | _ :: rest => audit_fixture_memo_proposal_expands rest
  end.

Fixpoint audit_fixture_memo_one_expands {F N E T CN CE CF SE XE OE BE LE RE WE}
    (events : list (audit_memo_legacy_one_event F N E T CN CE CF SE XE OE BE LE RE WE)) : nat :=
  match events with
  | [] => 0
  | AuditLegacyProjectionProposal body :: rest => audit_fixture_memo_proposal_expands body +
      audit_fixture_memo_one_expands rest
  | _ :: rest => audit_fixture_memo_one_expands rest
  end.

Fixpoint audit_fixture_memo_nodes_expands {F N E T CN CE CF SE XE OE BE LE RE WE MS}
    (events : list (audit_memo_legacy_nodes_event F N MS
      (audit_memo_legacy_one_event F N E T CN CE CF SE XE OE BE LE RE WE) CN)) : nat :=
  match events with
  | [] => 0
  | AuditMemoLegacyNodesOne _ _ _ _ body :: rest => audit_fixture_memo_one_expands body +
      audit_fixture_memo_nodes_expands rest
  | _ :: rest => audit_fixture_memo_nodes_expands rest
  end.

(** Both retained loads share one actual expansion and the second query hits the threaded memo. *)

Example audit_memo_legacy_fixture_reuses_query :
  def_of_load (fst audit_memo_legacy_fixture_plain) false = Some (MLive false) /\
  def_of_load (fst audit_memo_legacy_fixture_plain) true = Some (MLive false) /\
  let '(_, (_, _, body)) := audit_memo_legacy_fixture_counted in
  audit_fixture_memo_nodes_expands body = 1.
Proof.
  vm_compute.
  repeat split; reflexivity.
Qed.

(** The independent outer memo checker accepts both actual retained loads. *)

Example audit_memo_legacy_outer_checker_accepts :
  let '(accepted, _, _, _, _, _) := audit_memory_memo_legacy_check_counted
    bool_encoding bool_encoding unit_encoding audit_whole_node audit_whole_node audit_whole_node
    audit_whole_edge (fun edge => (edge, [tt])) (fun node => ([node], [tt]))
    (fun _ => (true, [tt])) (fun _ _ => (@None (memory_version bool bool), [tt]))
    (fun _ _ => (Some (@MemoryLive bool bool), [tt]))
    (fun node => (Some (node, 0), [tt])) audit_whole_regions audit_whole_regions
    audit_memo_legacy_fixture_graph audit_memo_legacy_fixture_effects
      audit_memo_legacy_fixture_memory
    false 1%positive audit_memo_legacy_fixture_state in
  accepted = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition audit_legacy_empty_graph : Graph.t bool bool :=
  Graph.Make [] [] (fun _ => []) (fun edge => edge) (fun edge => edge).

Definition audit_legacy_empty_state := memo_initial bool_encoding bool_encoding
  audit_legacy_empty_graph audit_memo_legacy_fixture_effects audit_memo_legacy_fixture_memory.

Definition audit_legacy_empty_projection := audit_memory_memo_legacy_project
  bool_encoding bool_encoding bool_encoding unit_encoding false audit_legacy_empty_graph
  audit_memo_legacy_fixture_effects (fun _ => []) (fun _ => []) audit_memo_legacy_fixture_memory
  audit_legacy_empty_state (fun node => Some (node, 0)) 1%positive.

(** An empty producer returns its exact incoming memo and answers every missing key with None. *)

Example audit_legacy_empty_preserves_state :
  snd audit_legacy_empty_projection = audit_legacy_empty_state /\
  def_of_load (fst audit_legacy_empty_projection) false = None /\
  def_of_load (fst audit_legacy_empty_projection) true = None.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The full legacy producer and outer checker also accept an empty graph. *)

Example audit_legacy_empty_checker_accepts :
  let '(accepted, _, _) := audit_legacy_projection_check_source_counted bool_encoding bool_encoding
    unit_encoding audit_whole_node audit_whole_node audit_whole_node audit_whole_edge
    (fun edge => (edge, [tt])) (fun _ => (@nil bool, [tt])) (fun edge => (edge, [tt]))
    (fun edge => (audit_memo_legacy_fixture_effects edge, [tt]))
    (fun _ _ => (@None (memory_version bool bool), [tt]))
    (fun _ _ => (Some (@MemoryLive bool bool), [tt])) (fun node => (Some (node, 0), [tt]))
    audit_whole_regions audit_whole_regions audit_legacy_empty_graph
      audit_memo_legacy_fixture_memory
    false 1%positive in accepted = true.
Proof.
  vm_compute; reflexivity.
Qed.

Definition audit_legacy_duplicate_graph : Graph.t bool bool :=
  Graph.Make [false] [false; true; false] (fun node => [node; node])
    (fun edge => edge) (fun _ => true).

Definition audit_legacy_duplicate_state := memo_initial bool_encoding bool_encoding
  audit_legacy_duplicate_graph audit_memo_legacy_fixture_effects audit_memo_legacy_fixture_memory.

Definition audit_legacy_duplicate_counted := audit_memory_memo_legacy_project_counted
  bool_encoding bool_encoding unit_encoding audit_whole_node audit_whole_node audit_whole_node
  audit_whole_edge (fun edge => (edge, [tt])) (fun node => ([node; node], [tt]))
  (fun _ => (true, [tt])) (fun _ _ => (@None (memory_version bool bool), [tt]))
  (fun _ _ => (Some (@MemoryLive bool bool), [tt])) (fun node => (Some (node, 0), [tt]))
  audit_whole_regions audit_whole_regions audit_legacy_duplicate_graph
  audit_memo_legacy_fixture_effects audit_memo_legacy_fixture_memory false 1%positive
  audit_legacy_duplicate_state.

(** Duplicate node and edge occurrences retain answers and reuse the same single expansion. *)

Example audit_legacy_duplicates_share_memo :
  let '(_, (pairs, _, body)) := audit_legacy_duplicate_counted in
  fst (audit_memo_legacy_lookup_counted audit_whole_node pairs false) = Some (MLive false) /\
  fst (audit_memo_legacy_lookup_counted audit_whole_node pairs true) = Some (MLive false) /\
  audit_fixture_memo_nodes_expands body = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Absent and explicitly missing candidates both return None through the actual trie read. *)

Example audit_legacy_missing_lookup :
  fst (@audit_memo_legacy_lookup_counted bool bool unit audit_whole_node Map.empty false) = None /\
  fst (audit_memo_legacy_lookup_counted audit_whole_node
    (Map.set bool_encoding false None (@Map.empty bool (option (mem_node bool bool)))) false) =
      None.
Proof.
  vm_compute; split; reflexivity.
Qed.

Definition audit_legacy_fixture_occurrence table before load :=
  @audit_legacy_occurrence_source_with bool bool unit unit unit unit unit unit unit unit unit
    audit_whole_node audit_whole_edge audit_whole_source (FinSet.of_list unit_encoding [tt])
    (FinSet.of_list bool_encoding [false; true]) table before load audit_whole_regions
    (fun _ _ _ => (MemoryClobberResult [MemoryLive] true, tt)) false 1%positive false.

Definition audit_legacy_fixture_table := memory_walk_effect_table unit_encoding audit_whole_graph
  (fun edge => fst (audit_whole_effects edge)).

(** Successful callbacks retain the exact load, guard, effect, before, read and query order. *)

Example audit_legacy_occurrence_order :
  match audit_legacy_fixture_occurrence audit_legacy_fixture_table audit_whole_before
    audit_whole_load with
  | (Some (MLive false), [AuditLegacySourceLoad false (Some (tt, 0)) [tt];
      AuditLegacySourceGuard guard; AuditLegacySourceEffect _;
      AuditLegacySourceBefore tt 0 (Some MemoryLive) [tt];
      AuditLegacySourceReadTest _ true; AuditLegacySourceReads false [] [tt];
      AuditLegacySourceClobbers (MemoryClobberResult [MemoryLive] true) tt;
      AuditLegacySourceReturn (Some (MLive false))]) => length guard = 7
  | _ => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

(** A missing effect returns before executing the before callback or a clobber query. *)

Example audit_legacy_effect_miss_skips_before :
  match audit_legacy_fixture_occurrence Map.empty audit_whole_before audit_whole_load with
  | (None, [AuditLegacySourceLoad _ _ _; AuditLegacySourceGuard _;
      AuditLegacySourceEffect _; AuditLegacySourceReturn None]) => True
  | _ => False
  end.
Proof.
  vm_compute; exact I.
Qed.

(** A missing before result retains that call and then skips reads and the memo query. *)

Example audit_legacy_before_miss_skips_query :
  match audit_legacy_fixture_occurrence audit_legacy_fixture_table
    (fun _ _ => (@None (memory_version bool unit), [tt])) audit_whole_load with
  | (None, [AuditLegacySourceLoad _ _ _; AuditLegacySourceGuard _;
      AuditLegacySourceEffect _; AuditLegacySourceBefore _ _ None [tt];
      AuditLegacySourceReturn None]) => True
  | _ => False
  end.
Proof.
  vm_compute; exact I.
Qed.

(** The first out-of-range effect index follows the missing-effect branch. *)

Example audit_legacy_effect_index_boundary :
  fst (audit_legacy_fixture_occurrence audit_legacy_fixture_table audit_whole_before
    (fun _ => (Some (tt, 1), [tt]))) = None.
Proof.
  vm_compute; reflexivity.
Qed.

(** A non-read effect retains its before call and read test, then skips the query. *)

Example audit_legacy_write_skips_query :
  let table := memory_walk_effect_table unit_encoding audit_whole_graph
    (fun _ => [@MemoryWrite unit MemoryAll]) in
  match audit_legacy_fixture_occurrence table audit_whole_before audit_whole_load with
  | (None, [AuditLegacySourceLoad _ _ _; AuditLegacySourceGuard _;
      AuditLegacySourceEffect _; AuditLegacySourceBefore _ _ _ _;
      AuditLegacySourceReadTest _ false; AuditLegacySourceReturn None]) => True
  | _ => False
  end.
Proof.
  vm_compute; exact I.
Qed.

(** A false node guard retains both membership probes in its seven-frame strict body. *)

Example audit_legacy_false_guard_is_strict :
  match @audit_legacy_occurrence_source_with bool bool unit unit unit unit unit unit unit unit unit
    audit_whole_node audit_whole_edge (fun _ => (true, [tt]))
    (FinSet.of_list unit_encoding [tt]) (FinSet.of_list bool_encoding [true])
    audit_legacy_fixture_table audit_whole_before audit_whole_load audit_whole_regions
    (fun _ _ _ => (MemoryClobberResult [MemoryLive] true, tt)) false 1%positive false with
  | (None, [AuditLegacySourceLoad _ _ _; AuditLegacySourceGuard body;
      AuditLegacySourceReturn None]) => length body = 7
  | _ => False
  end.
Proof.
  vm_compute; reflexivity.
Qed.

(** An incomplete multi-root result is rejected instead of selecting its first definition. *)

Example audit_legacy_multiple_roots_rejected :
  fst (@audit_legacy_finish_proposal bool bool unit unit unit unit unit unit unit unit unit
    audit_whole_source false (MemoryClobberResult [MemoryLive; MemoryDef tt 0] false)) = None.
Proof.
  vm_compute; reflexivity.
Qed.

(** Reversed footprints remain empty in the retained pair's actual checker. *)

Example audit_legacy_malformed_range_is_empty :
  legacy_disjoint_b unit_encoding [Footprint tt 2 1] [Footprint tt 0 3] = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The synthetic foreign client records one unit body at each actual callback invocation. *)

Definition audit_legacy_fixture_callback_source {A R} (call : A -> R * list unit)
    (argument : A) result body charge : Prop :=
  call argument = (result, body) /\ body = [tt] /\ charge = 1.

(** Constant-body foreign callbacks satisfy their source relation at every returned result. *)

Lemma audit_legacy_fixture_callback_adapter {A R} (call : A -> R * list unit) :
  (forall argument, snd (call argument) = [tt]) ->
  audit_external_callback_adapter call (@length unit)
    (audit_legacy_fixture_callback_source call) (fun _ => 1).
Proof.
  intro Hbody; constructor; intros argument result body Hcall.
  - unfold audit_legacy_fixture_callback_source.
    pose proof (Hbody argument) as Hunit; rewrite Hcall in Hunit; cbn [snd] in Hunit.
    subst body; repeat split; try exact Hcall; reflexivity.
  - pose proof (Hbody argument) as Hunit; rewrite Hcall in Hunit; cbn [snd] in Hunit.
    subst body; reflexivity.
Qed.

Definition audit_legacy_fixture_projection_work :=
  audit_legacy_projection_check_source_work bool_encoding (@length unit) (@length unit)
    (@length unit) (@length unit) (@length unit) (@length unit) (@length unit) (@length unit)
    (@length unit) (@length unit) (@length unit) (@length unit) (@length unit)
    audit_whole_legacy_pipeline.

Definition audit_legacy_fixture_projection_budget :=
  audit_legacy_projection_check_input_budget bool_encoding bool_encoding unit_encoding
    audit_whole_node audit_whole_edge audit_whole_node audit_whole_edge audit_whole_source
    audit_whole_out audit_whole_target audit_whole_effects audit_whole_operand audit_whole_before
    audit_whole_load audit_whole_regions audit_whole_regions
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ _ => 1) (fun _ _ => 1) audit_whole_graph audit_whole_memory false 2%positive.

(** The adapted whole bound prices the original nonempty client and all thirteen real callbacks. *)

Example audit_legacy_nonempty_adapted_receipt :
  audit_legacy_fixture_projection_work <= audit_legacy_fixture_projection_budget.
Proof.
  unfold audit_legacy_fixture_projection_work, audit_legacy_fixture_projection_budget,
    audit_whole_legacy_pipeline.
  eapply audit_legacy_projection_check_whole_input_bound_adapted;
    try (intros; reflexivity);
    apply audit_legacy_fixture_callback_adapter; intros; reflexivity.
Qed.

(** The lookup client retains the exact requested key and singleton foreign node body. *)

Example audit_legacy_missing_lookup_receipt :
  4 + audit_map_source_work (@length unit)
    (snd (@audit_memo_legacy_lookup_counted bool bool unit audit_whole_node Map.empty true)) <=
  9 + 1 + 5 * Pos.size_nat (encode bool_encoding true).
Proof.
  apply (audit_memo_legacy_lookup_source_bound bool bool unit audit_whole_node (@length unit)
    (fun _ => 1) (audit_legacy_fixture_callback_source audit_whole_node) Map.empty true).
  apply audit_legacy_fixture_callback_adapter; intro node; reflexivity.
Qed.

Fixpoint audit_fixture_memo_done_hits {N E CV CK NE}
    (events : list (audit_memo_event N E CV CK NE)) : nat :=
  match events with
  | [] => 0
  | AuditMemoLookup _ (Some (MemoDone _)) _ :: rest => S (audit_fixture_memo_done_hits rest)
  | _ :: rest => audit_fixture_memo_done_hits rest
  end.

Fixpoint audit_fixture_memo_proposal_shapes {F N E T CN CE SE XE OE BE LE RE}
    (events : list (audit_memo_legacy_proposal_event F N E T CN CE SE XE OE BE LE RE)) :
    list (nat * nat) :=
  match events with
  | [] => []
  | AuditLegacySourceClobbers _ receipt :: rest =>
      let body := audit_memo_body_events (audit_memo_legacy_execution receipt) in
      (audit_fixture_memo_expands body, audit_fixture_memo_done_hits body) ::
        audit_fixture_memo_proposal_shapes rest
  | _ :: rest => audit_fixture_memo_proposal_shapes rest
  end.

Fixpoint audit_fixture_memo_one_shapes {F N E T CN CE CF SE XE OE BE LE RE WE}
    (events : list (audit_memo_legacy_one_event F N E T CN CE CF SE XE OE BE LE RE WE)) :
    list (nat * nat) :=
  match events with
  | [] => []
  | AuditLegacyProjectionProposal body :: rest => audit_fixture_memo_proposal_shapes body ++
      audit_fixture_memo_one_shapes rest
  | _ :: rest => audit_fixture_memo_one_shapes rest
  end.

Fixpoint audit_fixture_memo_nodes_shapes {F N E T CN CE CF SE XE OE BE LE RE WE MS}
    (events : list (audit_memo_legacy_nodes_event F N MS
      (audit_memo_legacy_one_event F N E T CN CE CF SE XE OE BE LE RE WE) CN)) : list (nat * nat) :=
  match events with
  | [] => []
  | AuditMemoLegacyNodesOne _ _ _ _ body :: rest => audit_fixture_memo_one_shapes body ++
      audit_fixture_memo_nodes_shapes rest
  | _ :: rest => audit_fixture_memo_nodes_shapes rest
  end.

(** The first request expands, the second performs a completed lookup, in that strict order. *)

Example audit_legacy_receipts_show_second_hit :
  let '(_, (_, _, body)) := audit_memo_legacy_fixture_counted in
  audit_fixture_memo_nodes_shapes body = [(1, 0); (0, 1)].
Proof.
  vm_compute; reflexivity.
Qed.

(** The returned memo retains the completed entry written by the first actual query. *)

Example audit_legacy_returned_memo_contains_done :
  let '(_, (_, next, _)) := audit_memo_legacy_fixture_counted in
  Map.get (memo_key bool_encoding bool_encoding)
    (scope_code unit_encoding (MemoryRegions []), MemoryLive)
    (@memo_entries bool bool unit bool_encoding audit_memo_legacy_fixture_graph
      audit_memo_legacy_fixture_effects audit_memo_legacy_fixture_memory next) =
  Some (MemoDone [MemoryLive]).
Proof.
  vm_compute; reflexivity.
Qed.

(** The false first candidate retains the later candidate's entire checker branch. *)

Example audit_legacy_false_head_retains_tail :
  match audit_legacy_false_head_two_nodes_fixture with
  | (false, [AuditLegacyCheckerCase _; AuditLegacyCheckerCandidate false _ false _ _;
      AuditLegacyCheckerCase _; AuditLegacyCheckerCandidate true _ false _ _;
      AuditLegacyCheckerCase []]) => True
  | _ => False
  end.
Proof.
  vm_compute; exact I.
Qed.

Definition audit_legacy_empty_counted := audit_memory_memo_legacy_project_counted
  bool_encoding bool_encoding unit_encoding audit_whole_node audit_whole_node audit_whole_node
  audit_whole_edge (fun edge => (edge, [tt])) (fun _ => (@nil bool, [tt]))
  (fun edge => (edge, [tt])) (fun _ _ => (@None (memory_version bool bool), [tt]))
  (fun _ _ => (Some (@MemoryLive bool bool), [tt])) (fun node => (Some (node, 0), [tt]))
  audit_whole_regions audit_whole_regions audit_legacy_empty_graph audit_memo_legacy_fixture_effects
  audit_memo_legacy_fixture_memory false 1%positive audit_legacy_empty_state.

(** The empty counted run has the original state, no stored answers and only the terminal charge. *)

Example audit_legacy_empty_counted_receipt :
  let '(_, (pairs, next, body)) := audit_legacy_empty_counted in
  Map.elements pairs = [] /\ next = audit_legacy_empty_state /\
  audit_memo_legacy_nodes_source_work bool_encoding (@length unit) (@length unit) (@length unit)
    (@length unit) (@length unit) (@length unit) (@length unit) (@length unit) (@length unit)
    (@length unit) body = 2.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** A missing load emits its own body and return, without executing the guard. *)

Example audit_legacy_no_load_skips_guard :
  match audit_legacy_fixture_occurrence audit_legacy_fixture_table audit_whole_before
    (fun _ => (@None (unit * nat), [tt])) with
  | (None, [AuditLegacySourceLoad _ None [tt]; AuditLegacySourceReturn None]) => True
  | _ => False
  end.
Proof.
  vm_compute; exact I.
Qed.
