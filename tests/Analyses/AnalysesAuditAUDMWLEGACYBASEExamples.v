(** * Legacy checker audit examples

    These examples exercise strict branch traces and finite no-clobber decisions.
    For example, a rejected first candidate retains the second candidate's trace.
    Builds on: legacy checker observers and their adequacy proofs. *)

From Stdlib Require Import List PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesAuditMemoryLegacyCfg
  AnalysesAuditMemoryLegacyChecker AnalysesAuditMemoryLegacyGuard AnalysesAuditMemoryLegacyOverlap
  AnalysesAuditMemoryLegacySlice AnalysesAuditMemoryLegacySliceFull
  AnalysesAuditMemoryLegacySuccessor
  AnalysesAuditMemoryLegacyNoClobber.
Import List.ListNotations.

(** * Strict pair and node traces *)

(** The selected definition branch emits all six frames after a false load probe. *)
Example legacy_false_load_all_frames :
    match audit_legacy_false_load_pair_fixture with
    | (false, [AuditLegacyPairLoadProbe false false _;
        AuditLegacyPairOwnerCompare true true _ _ _ _ true _;
        AuditLegacyPairDefinitionProbe false false _; AuditLegacyPairSuccessors false [true] [tt];
        AuditLegacyPairReads false [] [tt]; AuditLegacyPairSlice _ _]) => true
    | _ => false
    end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** A false owner comparison still executes all six selected branch frames. *)
Example legacy_false_owner_all_frames :
    match audit_legacy_false_owner_pair_fixture with
    | (false, [AuditLegacyPairLoadProbe false true _;
        AuditLegacyPairOwnerCompare false true _ _ _ _ false _;
        AuditLegacyPairDefinitionProbe true false _; AuditLegacyPairSuccessors true [false] [tt];
        AuditLegacyPairReads false [] [tt]; AuditLegacyPairSlice _ _]) => true
    | _ => false
    end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The false first candidate retains the second candidate and terminal frame. *)
Example legacy_false_head_keeps_tail :
    match audit_legacy_false_head_two_nodes_fixture with
    | (false, [AuditLegacyCheckerCase _; AuditLegacyCheckerCandidate false _ false _ _;
        AuditLegacyCheckerCase _; AuditLegacyCheckerCandidate true _ false _ _;
        AuditLegacyCheckerCase []]) => true
    | _ => false
    end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** * End-to-end finite cases *)

Definition legacy_example_graph : Graph.t bool bool :=
  Graph.Make [false] [false] (fun _ => []) (fun e => e) (fun e => e).
Definition legacy_example_node n := (encode bool_encoding n, @nil unit).
Definition legacy_example_site (_ : unit) := (encode unit_encoding tt, @nil unit).
Definition legacy_example_out (_ : bool) := (@nil bool, @nil unit).
Definition legacy_example_target (e : bool) := (e, @nil unit).
Definition legacy_example_footprints (_ : bool) := (@nil (footprint unit), [tt]).

(** A reachable nonempty graph accepts the matching live-in candidate. *)
Example legacy_nonempty_checker_accepts :
    fst (audit_legacy_no_clobber_counted bool_encoding bool_encoding unit_encoding
      legacy_example_node legacy_example_node legacy_example_site legacy_example_out
      legacy_example_target legacy_example_footprints legacy_example_footprints true
      legacy_example_graph (fun _ => (Some (MLive true), [tt]))) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The same graph rejects a candidate owned by another function. *)
Example legacy_nonempty_checker_rejects :
    fst (audit_legacy_no_clobber_counted bool_encoding bool_encoding unit_encoding
      legacy_example_node legacy_example_node legacy_example_site legacy_example_out
      legacy_example_target legacy_example_footprints legacy_example_footprints true
      legacy_example_graph (fun _ => (Some (MLive false), [tt]))) = false.
Proof.
  vm_compute; reflexivity.
Qed.

(** An absent candidate imposes no pair check. *)
Example legacy_missing_candidate_accepts :
    fst (audit_legacy_no_clobber_counted bool_encoding bool_encoding unit_encoding
      legacy_example_node legacy_example_node legacy_example_site legacy_example_out
      legacy_example_target legacy_example_footprints legacy_example_footprints true
      legacy_example_graph (fun _ => (None, @nil unit))) = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** * Boundary and component observations *)

Definition legacy_duplicate_graph : Graph.t bool bool :=
  Graph.Make [false] [false; false] (fun _ => [true; true]) (fun _ => false) (fun _ => true).

(** Repeated targets retain their first occurrence in an indexed row with duplicate nodes. *)
Example legacy_cfg_duplicate_targets :
    let result := fst (audit_legacy_cfg_counted bool_encoding legacy_example_node
      (fun _ => ([true; true], [tt])) (fun e => (e, [tt])) legacy_duplicate_graph) in
    Graph.out result false = [(false, true)].
Proof.
  vm_compute; reflexivity.
Qed.

(** A lookup for a node absent from the normalized index returns no successors. *)
Example legacy_successor_missing_node :
    fst (audit_legacy_successors_counted bool_encoding legacy_example_node legacy_example_graph
      (prepare bool_encoding legacy_example_graph) true) = [].
Proof.
  vm_compute; reflexivity.
Qed.

(** Even a false guard retains both source callback bodies. *)
Example legacy_guard_retains_source_bodies :
    match audit_legacy_guard legacy_example_node legacy_example_node
      (fun e => (e, [tt])) FinSet.empty FinSet.empty false true with
    | (false, [AuditGuardSource _ _ [tt]; AuditGuardNodeEncode _ _ _;
        AuditGuardNodeEncode _ _ _; AuditGuardEqual _ _ _ _;
        AuditGuardSource _ _ [tt]; AuditGuardReached _ _ _; AuditGuardListed _ _ _]) => true
    | _ => false
    end = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** Adjacent ranges are disjoint, while overlapping ranges are rejected. *)
Example legacy_overlap_boundaries :
    (fst (audit_legacy_disjoint legacy_example_site [Footprint tt 0 1] [Footprint tt 1 2]),
     fst (audit_legacy_disjoint legacy_example_site [Footprint tt 0 2] [Footprint tt 1 2])) =
      (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** An empty node list terminates without any slice events. *)
Example legacy_slice_empty_nodes :
    audit_legacy_slice_nodes legacy_example_node legacy_example_site legacy_example_footprints []
      FinSet.empty FinSet.empty [] = (true, []).
Proof.
  reflexivity.
Qed.

(** The full slice still records both DFS executions for an empty node graph. *)
Example legacy_empty_full_slice_runs_both_walks :
    let graph := Graph.Make (@nil bool) (@nil bool) (fun _ => @nil bool) (fun e => e)
      (fun e => e) in
    let events := snd (audit_legacy_slice_full bool_encoding unit_encoding legacy_example_node
      legacy_example_site graph (prepare bool_encoding graph) legacy_example_footprints [] [] false)
      in
    (negb (Nat.eqb (length (audit_legacy_slice_forward_dfs events)) 0) &&
      negb (Nat.eqb (length (audit_legacy_slice_reverse_dfs events)) 0))%bool = true.
Proof.
  vm_compute; reflexivity.
Qed.

(** The uninstrumented checker accepts and rejects the same nonempty candidates. *)
Example legacy_original_checker_decisions :
    (no_clobber_check bool_encoding bool_encoding unit_encoding true legacy_example_graph
       (fun _ => []) (fun _ => []) (MemorySSA (fun _ => Some (MLive true))),
     no_clobber_check bool_encoding bool_encoding unit_encoding true legacy_example_graph
       (fun _ => []) (fun _ => []) (MemorySSA (fun _ => Some (MLive false)))) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** An accepted nonempty checker retains its definition and read callback bodies. *)
Example legacy_nonempty_checker_retains_bodies :
    let events := snd (audit_legacy_no_clobber_counted bool_encoding bool_encoding unit_encoding
      legacy_example_node legacy_example_node legacy_example_site legacy_example_out
      legacy_example_target legacy_example_footprints legacy_example_footprints true
      legacy_example_graph (fun _ => (Some (MLive true), [tt]))) in
    match audit_legacy_check_nodes_events events with
    | [AuditLegacyCheckerCase _;
       AuditLegacyCheckerCandidate false (MLive true) true [tt]
         [AuditLegacyPairLoadProbe false true _;
          AuditLegacyPairOwnerCompare true true _ _ _ _ true _;
          AuditLegacyPairReads false [] [tt]; AuditLegacyPairSlice _ _];
       AuditLegacyCheckerCase []] => true
    | _ => false
    end = true.
Proof.
  vm_compute; reflexivity.
Qed.
