(** * Guarded phi output observations

    These examples exercise retained and removed operand queries on a saved index.
    For example, a missing node skips the operand callback and representative lookup.
    Builds on: AnalysesAuditMemoryPhiOperandQuery and the phi output models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsTrie CollectionsMap
  CollectionsFinSet CollectionsAuditEncoding CollectionsAuditFinSet.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryEncoding.
From Galois.Analyses Require Import AnalysesAuditMemoryPhiOperandQuery
  AnalysesAuditMemoryPhiPlain AnalysesAuditMemoryPhiProducer AnalysesAuditMemoryPhiConsumer.
Import List.ListNotations.

Definition phi_test_old : memory_graph positive positive :=
  MemoryGraph [1%positive; 2%positive] [MemoryLive; MemoryPhi 1%positive; MemoryPhi 2%positive]
    (fun _ => MemoryLive) (fun _ _ => None) (fun _ => MemoryLive)
    (fun n _ => if Pos.eqb n 1%positive then Some (MemoryDef 1%positive 2) else None).

Definition phi_test_reps :
    Map.t (memory_version positive positive) (memory_version positive positive) :=
  Map.set (memory_version_encoding positive_encoding positive_encoding) (MemoryPhi 2%positive)
    MemoryLive Map.empty.

Definition phi_test_base (input : positive * option positive) :=
  (memory_operand phi_test_old (fst input) (snd input), [tt; tt]).

Definition phi_test_version :=
  audit_memory_version_encode audit_positive_encode audit_positive_encode.

Definition phi_test_index :=
  audit_phi_operand_output_index positive_encoding positive_encoding phi_test_old phi_test_reps.

Definition phi_test_saved :=
  audit_phi_operand_saved_query audit_positive_encode phi_test_version phi_test_index
    phi_test_base phi_test_reps.

(** The output retains the first phi, removes the second, and guards its operand. *)
Example phi_test_output_fields :
  let output := audit_phi_producer_output positive_encoding positive_encoding phi_test_old
    phi_test_reps in
  memory_phis output = [1%positive] /\
  memory_versions output = [MemoryLive; MemoryPhi 1%positive] /\
  memory_operand output 1%positive None = Some (MemoryDef 1%positive 2) /\
  memory_operand output 2%positive None = None /\
  memory_operand output 3%positive None = None.
Proof.
  vm_compute.
  repeat split; reflexivity.
Qed.

(** The removed node has only a probe and an absent event. *)
Example phi_test_removed_skips_callbacks :
  match snd (phi_test_saved (2%positive, None)) with
  | [AuditPhiOperandProbe _ false _; AuditPhiOperandAbsent] => True
  | _ => False
  end.
Proof.
  vm_compute.
  exact I.
Qed.

(** The captured index is reused for a hit, miss, and repeated hit. *)
Example phi_test_saved_repeated :
  map (fun input => fst (phi_test_saved input))
    [(1%positive, None); (2%positive, None); (1%positive, None)] =
  [Some (MemoryDef 1%positive 2); None; Some (MemoryDef 1%positive 2)].
Proof.
  vm_compute.
  reflexivity.
Qed.

(** An empty captured set skips even a callback that would return a value. *)
Example phi_test_empty :
  let run := audit_phi_output_operand_call audit_positive_encode phi_test_version FinSet.empty
    phi_test_base phi_test_reps (1%positive, None) in
  fst run = None /\
  match snd run with
  | [AuditPhiOperandProbe _ false _; AuditPhiOperandAbsent] => True
  | _ => False
  end.
Proof.
  vm_compute.
  split; [reflexivity | exact I].
Qed.

(** A retained key with no operand executes the base but skips representative lookup. *)
Example phi_test_missing_operand :
  let base := fun _ : positive * option positive =>
    (@None (memory_version positive positive), [tt]) in
  match snd (audit_phi_output_operand_call audit_positive_encode phi_test_version phi_test_index
    base phi_test_reps (1%positive, None)) with
  | [AuditPhiOperandProbe _ true _; AuditPhiOperandBody [AuditPhiClosureCall _ None _]] => True
  | _ => False
  end.
Proof.
  vm_compute.
  exact I.
Qed.

(** Even a malformed stored key is probed by its trie position, as the model specifies. *)
Example phi_test_malformed_index :
  let malformed : FinSet.t positive := Trie.set 1%positive (3%positive, tt) Trie.empty in
  let run := audit_phi_output_operand_call audit_positive_encode phi_test_version malformed
    phi_test_base phi_test_reps (1%positive, None) in
  fst run = Some (MemoryDef 1%positive 2) /\
  match snd run with
  | [AuditPhiOperandProbe _ true _; AuditPhiOperandBody _] => True
  | _ => False
  end.
Proof.
  vm_compute.
  split; [reflexivity | exact I].
Qed.

(** A present representative replaces the callback's definition version. *)
Example phi_test_representative_hit :
  let reps := Map.set (memory_version_encoding positive_encoding positive_encoding)
    (MemoryDef 1%positive 2) (MemoryPhi 1%positive) phi_test_reps in
  fst (audit_phi_output_operand_call audit_positive_encode phi_test_version phi_test_index
    phi_test_base reps (1%positive, None)) = Some (MemoryPhi 1%positive).
Proof.
  vm_compute.
  reflexivity.
Qed.

(** The actual composite version encoder accounts for a definition and its unary index. *)
Example phi_test_source_receipts :
  audit_phi_operand_query_source_work audit_basic_encoding_work
    (audit_memory_version_work audit_basic_encoding_work audit_basic_encoding_work) (@length unit)
    (snd (phi_test_saved (1%positive, None))) = 104 /\
  audit_phi_operand_query_source_work audit_basic_encoding_work
    (audit_memory_version_work audit_basic_encoding_work audit_basic_encoding_work) (@length unit)
    (snd (phi_test_saved (2%positive, None))) = 15.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** Plain and counted construction expose the same guarded operands for this fixture. *)
Example phi_test_plain_counted_outputs :
  let plain := audit_phi_compute_output positive_encoding positive_encoding phi_test_old
    phi_test_reps in
  let counted := fst (audit_phi_producer_output_counted positive_encoding positive_encoding
    audit_positive_encode phi_test_version phi_test_old phi_test_reps) in
  memory_operand plain 1%positive None = memory_operand counted 1%positive None /\
  memory_operand plain 2%positive None = memory_operand counted 2%positive None.
Proof.
  vm_compute.
  split; reflexivity.
Qed.

(** The producer's set-build trace records the same persistent index used by the saved query. *)
Example phi_test_captured_output_index :
  let kept := fst (audit_phi_output_keep_phis positive_encoding positive_encoding
    audit_positive_encode phi_test_version phi_test_reps (memory_phis phi_test_old)) in
  let '(captured, calls) := audit_finset_of_list audit_positive_encode kept in
  captured = phi_test_index /\
  In (AuditSetFold [] captured) calls /\
  In (AuditPhiOutputSetBuild calls)
    (snd (audit_phi_producer_output_counted positive_encoding positive_encoding
      audit_positive_encode phi_test_version phi_test_old phi_test_reps)).
Proof.
  vm_compute.
  intuition.
Qed.

(** The independent direct expression yields the same exact branch receipts. *)
Example phi_test_direct_receipts :
  audit_phi_operand_query_direct_work audit_positive_encode phi_test_version phi_test_base
    audit_basic_encoding_work
    (audit_memory_version_work audit_basic_encoding_work audit_basic_encoding_work) (@length unit)
    phi_test_index phi_test_reps (1%positive, None) = 104 /\
  audit_phi_operand_query_direct_work audit_positive_encode phi_test_version phi_test_base
    audit_basic_encoding_work
    (audit_memory_version_work audit_basic_encoding_work audit_basic_encoding_work) (@length unit)
    phi_test_index phi_test_reps (2%positive, None) = 15.
Proof.
  vm_compute.
  split; reflexivity.
Qed.
