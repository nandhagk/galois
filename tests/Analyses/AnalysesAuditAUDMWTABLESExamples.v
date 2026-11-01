(** * Memory table observer examples

    These examples exercise empty and duplicate inputs, lookup failures and interval boundaries.
    For example, adjacent half-open ranges are disjoint while overlapping ranges are not.
    Builds on: the memory table and raw successor observers. *)

From Stdlib Require Import List PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesAuditMemoryDisjoint
  AnalysesAuditMemoryDistinct AnalysesAuditMemoryEffects AnalysesAuditMemoryIndex
  AnalysesAuditMemoryTable AnalysesAuditMemoryRawNext.
Import List.ListNotations.

Definition fixture_enc (p : positive) := (p, @nil unit).

Definition fixture_left := Footprint 1%positive 0%Z 4%Z.

Definition fixture_adjacent := Footprint 1%positive 4%Z 7%Z.

Definition fixture_overlap := Footprint 1%positive 3%Z 7%Z.

Definition fixture_effect : memory_effect positive := MemoryWrite (MemoryRegions [fixture_left]).

(** Empty inputs have no pairs, and adjacent endpoints do not overlap. *)
Example fixture_disjoint_boundaries :
  fst (audit_footprints_disjoint fixture_enc [] [fixture_left]) = true /\
  fst (audit_footprints_disjoint fixture_enc [fixture_left] [fixture_adjacent]) = true /\
  fst (audit_footprints_disjoint fixture_enc [fixture_left] [fixture_overlap]) = false /\
  audit_disjoint_pairs (snd (audit_footprints_disjoint fixture_enc
    [fixture_left; fixture_overlap] [fixture_adjacent; fixture_left])) = 4.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Duplicate keys retain first-occurrence ordering. *)
Example fixture_distinct_duplicate :
  fst (audit_memory_distinct fixture_enc [1%positive; 2%positive; 1%positive]) =
    [1%positive; 2%positive].
Proof.
  vm_compute; reflexivity.
Qed.

(** Tail-first indexing retains the first occurrence's value and returns missing keys as absent. *)
Example fixture_index_duplicate_and_missing :
  let value := fun k : positive => (k, @nil unit) in
  let index := fst (audit_memory_result_index fixture_enc value [1%positive; 1%positive]) in
  Map.get positive_encoding 1%positive index = Some 1%positive /\
  Map.get positive_encoding 2%positive index = None /\
  length (snd (audit_memory_result_index fixture_enc value [1%positive; 1%positive])) = 3.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** The single effect is present at index zero; index one and the other edge are missing. *)
Example fixture_effect_lookup :
  let row := fst (audit_memory_effects_from 0 [fixture_effect]) in
  let table := Map.set positive_encoding 1%positive row Map.empty in
  fst (audit_memory_effect_get fixture_enc table 1%positive 0) = Some fixture_effect /\
  fst (audit_memory_effect_get fixture_enc table 1%positive 1) = None /\
  fst (audit_memory_effect_get fixture_enc table 2%positive 0) = None /\
  length (snd (audit_memory_effect_get fixture_enc table 2%positive 0)) = 1.
Proof.
  vm_compute; repeat split; reflexivity.
Qed.

(** Duplicate outgoing edges still yield one stored row, with the expected first effect. *)
Example fixture_table_duplicate :
  let out := fun _ : positive => ([1%positive; 1%positive], @nil unit) in
  let effects := fun _ : positive => ([fixture_effect], @nil unit) in
  let table := fst (audit_memory_effect_table fixture_enc out effects [1%positive]) in
  fst (audit_memory_effect_get fixture_enc table 1%positive 0) = Some fixture_effect /\
  fst (audit_memory_effect_get fixture_enc table 2%positive 0) = None.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** A missing effect skips the before callback even if that callback returns a version. *)
Example fixture_raw_missing_effect :
  let incoming := fun _ : positive => (@nil positive, @nil unit) in
  let operand := fun (_ : positive) (_ : option positive) =>
    (@None (memory_version positive positive), @nil unit) in
  let before := fun (_ : positive) (_ : nat) =>
    (Some (@MemoryLive positive positive), [tt]) in
  let events := snd (audit_memory_raw_next fixture_enc fixture_enc Map.empty incoming operand before
    MemoryAll (MemoryDef 1%positive 0)) in
  length events = 2 /\
  (forall e i result body, ~ In (AuditRawBefore e i result body) events).
Proof.
  vm_compute; split.
  - reflexivity.
  - intros e i result body [Hbranch | [Heffect | Hempty]].
    + discriminate Hbranch.
    + discriminate Heffect.
    + exact Hempty.
Qed.

(** Phi successors retain the missing operand event and the later present edge operand. *)
Example fixture_raw_phi_operands :
  let incoming := fun _ : positive => ([2%positive], @nil unit) in
  let operand := fun (_ : positive) (key : option positive) =>
    (match key with
     | None => None
     | Some e => Some (MemoryDef e 0)
     end, [tt]) in
  let before := fun (_ : positive) (_ : nat) =>
    (@None (memory_version positive positive), @nil unit) in
  let run := audit_memory_raw_next fixture_enc fixture_enc Map.empty incoming operand before
    MemoryAll (MemoryPhi 1%positive) in
  fst run = [MemoryDef 2%positive 0] /\ length (snd run) = 4.
Proof.
  vm_compute; split; reflexivity.
Qed.

(** Present effect and before lookups use the adjacent-range disjointness result. *)
Example fixture_raw_present_effect :
  let incoming := fun _ : positive => (@nil positive, @nil unit) in
  let operand := fun (_ : positive) (_ : option positive) =>
    (@None (memory_version positive positive), @nil unit) in
  let before := fun (_ : positive) (_ : nat) =>
    (Some (@MemoryLive positive positive), [tt]) in
  let row := fst (audit_memory_effects_from 0 [fixture_effect]) in
  let table := Map.set positive_encoding 1%positive row Map.empty in
  let run := audit_memory_raw_next fixture_enc fixture_enc table incoming operand before
    (MemoryRegions [fixture_adjacent]) (MemoryDef 1%positive 0) in
  fst run = [MemoryLive] /\ length (snd run) = 4.
Proof.
  vm_compute; split; reflexivity.
Qed.
