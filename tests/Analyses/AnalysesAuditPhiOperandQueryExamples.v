(** * Guarded operand query receipts

    These examples observe the saved set, callback order and exact query work.
    For example, a missing set position skips both the operand and representative callbacks.
    Builds on: guarded operand query adequacy and canonical collection models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsTrie CollectionsMap CollectionsFinSet
  CollectionsAuditCost CollectionsAuditTrie CollectionsAuditFinSet CollectionsAuditMap
  CollectionsAuditEncoding.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryPhiConsumer AnalysesAuditMemoryPhiOperandQuery
  AnalysesAuditMemoryPhiOperandQueryAdequacy.
Import List.ListNotations.

Definition query_test_node (n : positive) := (n, [tt]).
Definition query_test_version (_ : memory_version positive positive) := (1%positive, [tt; tt]).
Definition query_test_base (_ : positive * option positive) :=
  (Some (@MemoryLive positive positive), [tt; tt; tt]).
Definition query_test_kept : FinSet.t positive := Trie.set 1%positive (3%positive, tt) Trie.empty.
Definition query_test_reps :
    Map.t (memory_version positive positive) (memory_version positive positive) :=
  Trie.set 1%positive (MemoryPhi 3%positive, MemoryPhi 2%positive) Trie.empty.
Definition query_test_saved :=
  audit_phi_operand_saved_query query_test_node query_test_version query_test_kept
    query_test_base query_test_reps.
Definition query_test_work :=
  @audit_phi_operand_query_source_work positive positive unit unit unit
    (@length unit) (@length unit) (@length unit).

(** A retained malformed key is read at its trie position and uses the stored representative. *)
Example query_test_malformed_hit :
  fst (query_test_saved (1%positive, None)) = Some (MemoryPhi 2%positive) /\
  match snd (query_test_saved (1%positive, None)) with
  | [AuditPhiOperandProbe _ true [_];
      AuditPhiOperandBody [AuditPhiClosureCall _ (Some MemoryLive) _;
        AuditPhiClosureRead _ (Some (MemoryPhi 2%positive)) [_]]] => True
  | _ => False
  end.
Proof.
  vm_compute.
  split; [reflexivity|exact I].
Qed.

(** A removed node and an empty set skip the base and representative callbacks. *)
Example query_test_absent :
  fst (query_test_saved (2%positive, None)) = None /\
  (match snd (query_test_saved (2%positive, None)) with
   | [AuditPhiOperandProbe _ false [_]; AuditPhiOperandAbsent] => True
   | _ => False
   end) /\
  fst (audit_phi_output_operand_call query_test_node query_test_version FinSet.empty
    query_test_base query_test_reps (1%positive, None)) = None.
Proof.
  vm_compute.
  repeat split; reflexivity.
Qed.

(** Missing operands skip the map read, while a missing representative preserves the operand. *)
Example query_test_body_misses :
  let missing := fun _ : positive * option positive =>
    (@None (memory_version positive positive), [tt]) in
  (match snd (audit_phi_output_operand_call query_test_node query_test_version query_test_kept
    missing query_test_reps (1%positive, None)) with
   | [AuditPhiOperandProbe _ true _; AuditPhiOperandBody [AuditPhiClosureCall _ None _]] => True
   | _ => False
   end) /\
  fst (audit_phi_output_operand_call query_test_node query_test_version query_test_kept
    query_test_base Map.empty (1%positive, None)) = Some MemoryLive.
Proof.
  vm_compute.
  split; [exact I|reflexivity].
Qed.

(** The same captured set serves a hit, miss, and repeated hit with exact receipts. *)
Example query_test_repeated_receipts :
  map (fun input => fst (query_test_saved input))
    [(1%positive, None); (2%positive, None); (1%positive, None)] =
      [Some (MemoryPhi 2%positive); None; Some (MemoryPhi 2%positive)] /\
  map (fun input => query_test_work (snd (query_test_saved input)))
    [(1%positive, None); (2%positive, None); (1%positive, None)] = [34; 15; 34].
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** The concrete definition encoder records the actual edge callback before its lookup. *)
Example query_test_concrete_version_callback :
  let version := audit_memory_version_encode query_test_node query_test_node in
  let base := fun _ : positive * option positive =>
    (Some (MemoryDef 1%positive 2), [tt; tt; tt]) in
  match snd (audit_phi_output_operand_call query_test_node version query_test_kept base Map.empty
    (1%positive, None)) with
  | [AuditPhiOperandProbe _ true _;
      AuditPhiOperandBody [AuditPhiClosureCall _ _ _;
        AuditPhiClosureRead _ None [AuditMapGet _ _ _ None
          [AuditVersionDef 1%positive 2 _ (AuditPairFirst 1%positive 1%positive [tt] :: _)] _]]] =>
      True
  | _ => False
  end.
Proof.
  vm_compute.
  exact I.
Qed.

(** The universal adequacy theorem applies to the malformed-key representative hit. *)
Example query_test_adequacy_consumer :
  query_test_work (snd (query_test_saved (1%positive, None))) =
    audit_phi_operand_query_direct_work query_test_node query_test_version query_test_base
      (@length unit) (@length unit) (@length unit) query_test_kept query_test_reps
      (1%positive, None).
Proof.
  apply audit_phi_operand_query_source_adequate.
Qed.
