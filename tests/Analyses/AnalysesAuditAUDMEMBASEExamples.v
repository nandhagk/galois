(** * Shared memory encoding examples

    These examples observe the counted encoders, scope budgets and empty memo entries.
    For example, a repeated region contributes its encoding work twice.
    Builds on: memory encoding and state adequacy. *)

From Stdlib Require Import List PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow AnalysesMemoryWalk
  AnalysesAuditMemoryEncoding AnalysesAuditMemoryState AnalysesAuditMemoryEncodingAdequacy
  AnalysesAuditMemoryStateAdequacy.
Import List.ListNotations.

(** * Fixtures *)

Definition example_code (p : positive) : positive * list unit := (p, [tt]).
Definition example_work (events : list unit) : nat := length events.
Definition example_region : footprint positive := Footprint 1%positive (-1) 0.

(** * Encoding and memo observations *)

(** Live encoding does not call either supplied encoder. *)
Example live_version_tag :
  audit_memory_version_encode example_code example_code (@MemoryLive positive positive) =
    (1%positive, [AuditVersionLive]).
Proof.
  reflexivity.
Qed.

(** A definition version with zero index erases to its canonical code. *)
Example definition_version_erases :
  fst (audit_memory_version_encode example_code example_code (MemoryDef 2%positive 0)) =
    encode (memory_version_encoding positive_encoding positive_encoding) (MemoryDef 2%positive 0).
Proof.
  reflexivity.
Qed.

(** The actual definition event retains its edge and zero index. *)
Example definition_version_event :
  match snd (audit_memory_version_encode example_code example_code (MemoryDef 2%positive 0)) with
  | [AuditVersionDef edge index _ _] => (edge, index)
  | _ => (1%positive, 1)
  end = (2%positive, 0).
Proof.
  reflexivity.
Qed.

(** Empty regions and all memory use distinct tagged scope codes. *)
Example empty_scope_distinct :
  Pos.eqb (fst (audit_memory_scope_encode example_code (MemoryRegions [])))
    (fst (audit_memory_scope_encode example_code MemoryAll)) = false.
Proof.
  reflexivity.
Qed.

(** Empty regions fit their budget without any footprint child calls. *)
Example empty_regions_budget :
  Nat.leb
    (audit_memory_scope_work example_work
      (snd (audit_memory_scope_encode example_code (MemoryRegions []))))
    (audit_memory_scope_budget example_code example_work (MemoryRegions [])) = true.
Proof.
  reflexivity.
Qed.

(** Negative and zero endpoints erase to the original footprint encoding. *)
Example footprint_erases :
  fst (audit_memory_footprint_encode example_code example_region) =
    encode (footprint_encoding positive_encoding) example_region.
Proof.
  reflexivity.
Qed.

(** Duplicate regions are retained and their captured work fits the original-input budget. *)
Example duplicate_scope_budget :
  Nat.leb
    (audit_memory_scope_work example_work
      (snd (audit_memory_scope_encode example_code
        (MemoryRegions [example_region; example_region]))))
    (audit_memory_scope_budget example_code example_work
      (MemoryRegions [example_region; example_region])) =
    true.
Proof.
  reflexivity.
Qed.

(** Duplicate regions have a different code from a singleton region. *)
Example duplicate_scope_code :
  Pos.eqb (scope_code positive_encoding (MemoryRegions [example_region; example_region]))
    (scope_code positive_encoding (MemoryRegions [example_region])) = false.
Proof.
  reflexivity.
Qed.

(** Memo-key erasure retains the scope code and definition version. *)
Example memo_key_erases :
  fst (audit_memory_memo_key_encode example_code example_code
    (1%positive, MemoryDef 2%positive 0)) =
  encode (memo_key positive_encoding positive_encoding) (1%positive, MemoryDef 2%positive 0).
Proof.
  reflexivity.
Qed.

(** A missing version in an empty memo map has no entry. *)
Example empty_memo_lookup :
  Map.get (memo_key positive_encoding positive_encoding) (1%positive, MemoryLive)
    (@Map.empty (positive * memory_version positive positive) (memo_entry positive positive)) =
    None.
Proof.
  reflexivity.
Qed.

(** A busy cut returns its starting version and marks the result incomplete. *)
Example busy_cut_observation :
  busy_cut (@MemoryLive positive positive) = MemoryClobberResult [MemoryLive] false.
Proof.
  reflexivity.
Qed.

(** A phi event captures the actual node code and child event. *)
Example phi_version_event :
  audit_memory_version_encode example_code example_code (@MemoryPhi positive positive 2%positive) =
    (4%positive, [AuditVersionPhi 2%positive 2%positive [tt]]).
Proof.
  reflexivity.
Qed.

(** The all-memory branch has exactly two work units and fits its boundary budget. *)
Example all_scope_exact_budget :
  audit_memory_scope_work example_work (snd (audit_memory_scope_encode example_code MemoryAll)) =
    audit_memory_scope_budget example_code example_work MemoryAll.
Proof.
  reflexivity.
Qed.

(** Signed endpoint changes are visible in the actual footprint code. *)
Example footprint_boundary_code :
  Pos.eqb (fst (audit_memory_footprint_encode example_code example_region))
    (fst (audit_memory_footprint_encode example_code (Footprint 1%positive 0 0))) = false.
Proof.
  reflexivity.
Qed.

(** Setting the same memo key twice retains the later entry, while another key is absent. *)
Example duplicate_memo_key :
  let key := (1%positive, @MemoryLive positive positive) in
  let entries := Map.set (memo_key positive_encoding positive_encoding) key
    (MemoDone [MemoryLive])
    (Map.set (memo_key positive_encoding positive_encoding) key MemoBusy
      (@Map.empty (positive * memory_version positive positive) (memo_entry positive positive))) in
  Map.get (memo_key positive_encoding positive_encoding) key entries =
    Some (MemoDone [MemoryLive]) /\
  Map.get (memo_key positive_encoding positive_encoding) (2%positive, MemoryLive) entries = None.
Proof.
  split; reflexivity.
Qed.
