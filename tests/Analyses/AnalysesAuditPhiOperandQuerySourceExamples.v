(** * Saved phi operand source examples

    These examples exercise the actual persistent output set and its saved queries.
    For example, a removed phi skips the operand callback while a retained phi records it.
    Builds on: phi operand query source adequacy. *)

From Stdlib Require Import List PArith NArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsTrie CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditMap.
From Galois.Graph Require Import GraphCore GraphAuditBase.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryPhiProducer AnalysesAuditMemoryPhiConsumer
  AnalysesAuditMemoryPhiOperandQuery AnalysesAuditMemoryPhiOperandQuerySourceAdequacy
  AnalysesAuditMemoryPhiSetup.
Import List.ListNotations.

Definition source_operand (_ : positive) (key : option positive) :
    option (memory_version positive positive) * list unit :=
  match key with
  | None => (Some MemoryLive, [tt])
  | Some 1%positive => (None, [tt; tt])
  | Some n => (Some (MemoryPhi n), [tt])
  end.

Definition source_old : memory_graph positive positive :=
  MemoryGraph [1%positive; 2%positive] [MemoryLive; MemoryPhi 1%positive; MemoryPhi 2%positive]
    (fun _ => MemoryLive) (fun _ _ => None) (fun _ => MemoryLive)
    (fun n key => fst (source_operand n key)).

Definition source_empty : memory_graph positive positive :=
  MemoryGraph [] [] (fun _ => MemoryLive) (fun _ _ => None) (fun _ => MemoryLive)
    (fun n key => fst (source_operand n key)).

Definition source_reps :
    Map.t (memory_version positive positive) (memory_version positive positive) :=
  Map.set (memory_version_encoding positive_encoding positive_encoding)
    (MemoryPhi 2%positive) MemoryLive Map.empty.

Definition source_version :=
  audit_memory_version_encode audit_positive_encode audit_positive_encode.

Definition source_kept := fst (audit_phi_output_keep_phis positive_encoding positive_encoding
  audit_positive_encode source_version source_reps (memory_phis source_old)).

Definition source_build := audit_finset_of_list audit_positive_encode source_kept.

Definition source_saved := audit_phi_operand_saved_query audit_positive_encode source_version
  (fst source_build) (fun input => source_operand (fst input) (snd input)) source_reps.

Definition source_work input := N.of_nat (audit_phi_operand_query_source_work
  audit_basic_encoding_work (audit_memory_version_work audit_basic_encoding_work
    audit_basic_encoding_work) (@length unit) (snd (source_saved input))).

(** The empty constructor captures its terminal state and omits the operand callback. *)
Example source_empty_capture :
  let kept := fst (audit_phi_output_keep_phis positive_encoding positive_encoding
    audit_positive_encode source_version Map.empty (memory_phis source_empty)) in
  let '(captured, calls) := audit_finset_of_list audit_positive_encode kept in
  captured = FinSet.empty /\ In (AuditSetFold [] captured) calls /\
  match snd (audit_phi_operand_saved_query audit_positive_encode source_version captured
    (fun input => source_operand (fst input) (snd input)) Map.empty (1%positive, None)) with
  | [AuditPhiOperandProbe _ false _; AuditPhiOperandAbsent] => True
  | _ => False
  end.
Proof.
  vm_compute; intuition.
Qed.

(** The set-build event contains the same final set used by the returned graph. *)
Example source_persistent_capture :
  let '(captured, calls) := source_build in
  captured = audit_phi_operand_output_index positive_encoding positive_encoding
    source_old source_reps /\
  In (AuditSetFold [] captured) calls /\
  In (AuditPhiOutputSetBuild calls)
    (snd (audit_phi_producer_output_counted positive_encoding positive_encoding
      audit_positive_encode source_version source_old source_reps)) /\
  memory_phis (audit_phi_producer_output positive_encoding positive_encoding
    source_old source_reps) =
    [1%positive] /\
  memory_versions (audit_phi_producer_output positive_encoding positive_encoding source_old
    source_reps) = [MemoryLive; MemoryPhi 1%positive].
Proof.
  vm_compute; intuition.
Qed.

(** Hit, removed node, absent operand and repeated hit retain results and exact work. *)
Example source_repeated_queries :
  map (fun input => fst (source_saved input))
    [(1%positive, None); (2%positive, None); (1%positive, Some 1%positive);
      (1%positive, Some 2%positive); (1%positive, None)] =
    [Some MemoryLive; None; None; Some MemoryLive; Some MemoryLive] /\
  map source_work [(1%positive, None); (2%positive, None); (1%positive, Some 1%positive);
    (1%positive, Some 2%positive); (1%positive, None)] = [29%N; 15%N; 18%N; 42%N; 29%N].
Proof.
  vm_compute; split; reflexivity.
Qed.

(** The hit records the original body; the miss and missing operand skip later calls. *)
Example source_callback_branches :
  (match snd (source_saved (1%positive, Some 2%positive)) with
   | [AuditPhiOperandProbe _ true _;
      AuditPhiOperandBody [AuditPhiClosureCall _ (Some (MemoryPhi _)) [tt];
        AuditPhiClosureRead _ (Some MemoryLive) _]] => True
   | _ => False
   end) /\
  (match snd (source_saved (2%positive, None)) with
   | [AuditPhiOperandProbe _ false _; AuditPhiOperandAbsent] => True
   | _ => False
   end) /\
  (match snd (source_saved (1%positive, Some 1%positive)) with
   | [AuditPhiOperandProbe _ true _; AuditPhiOperandBody [AuditPhiClosureCall _ None [tt; tt]]] =>
      True
   | _ => False
   end).
Proof.
  vm_compute; intuition.
Qed.

(** A malformed stored key is observed by its actual trie position. *)
Example source_malformed_position :
  let malformed : FinSet.t positive := Trie.set 1%positive (7%positive, tt) Trie.empty in
  let run := audit_phi_operand_saved_query audit_positive_encode source_version malformed
    (fun input => source_operand (fst input) (snd input)) source_reps (1%positive, None) in
  fst run = Some MemoryLive /\
  match snd run with
  | [AuditPhiOperandProbe _ true _; AuditPhiOperandBody _] => True
  | _ => False
  end.
Proof.
  vm_compute; intuition.
Qed.

(** A nonempty complete producer and its saved miss expose their separate source receipts. *)
Example source_complete_receipts :
  let graph : Graph.t unit unit :=
    {| Graph.entries := [tt]; Graph.nodes := [tt]; Graph.out := fun _ => [];
       Graph.source := fun _ => tt; Graph.target := fun _ => tt |} in
  let old : memory_graph unit unit :=
    MemoryGraph [tt] [MemoryLive; MemoryPhi tt] (fun _ => MemoryPhi tt)
      (fun _ _ => None) (fun _ => MemoryLive)
      (fun _ key =>
        match key with
        | None => Some MemoryLive
        | Some _ => None
        end) in
  let enc := fun _ : unit => (1%positive, [tt]) in
  let operand := fun n key => (memory_operand old n key, [tt]) in
  let '(_, preparation, run) := audit_memory_phi_prune_counted unit_encoding unit_encoding enc enc
    (fun _ => (@nil unit, [tt])) (fun _ => (tt, [tt])) operand graph
    (fun _ => @nil (memory_effect unit)) old in
  let version := audit_memory_version_encode enc enc in
  let reps := audit_phi_run_representatives unit_encoding run in
  let kept := fst (audit_phi_output_keep_phis unit_encoding unit_encoding enc version reps
    (memory_phis old)) in
  let captured := fst (audit_finset_of_list enc kept) in
  let query := audit_phi_operand_saved_query enc version captured
    (fun args => operand (fst args) (snd args)) reps (tt, None) in
  N.of_nat (audit_prepare_source_work
    (audit_phi_input_graph_body_work (@length unit) (@length unit) (@length unit)) preparation +
    audit_phi_producer_work (@length unit) (@length unit) (audit_map_source_work (@length unit))
      (@length unit) (audit_memory_version_work (@length unit) (@length unit)) unit_encoding run) =
    5252%N /\
  fst query = None /\
  N.of_nat (audit_phi_operand_query_source_work (@length unit)
    (audit_memory_version_work (@length unit) (@length unit)) (@length unit) (snd query)) = 10%N.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.
