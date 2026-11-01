(** * Counted memory keys and scopes

    These adapters compose the actual version, footprint, scope and memo-key encodings.
    For example, a definition version records its edge encoder and unary index conversion.
    Builds on: G4 memory semantics and the shared composite-encoding observers. *)

From Stdlib Require Import List PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow.
From Galois.Collections Require Import CollectionsAuditEncoding.
Import List.ListNotations.

(** The scope and key encodings are shared before the memo-state module is defined. *)
Definition scope_code {T} (ET : encoding T) (q : memory_scope T) : positive :=
  match q with
  | MemoryAll => encode (sum_encoding unit_encoding (list_encoding (footprint_encoding ET))) (inl
    tt)
  | MemoryRegions fs =>
      encode (sum_encoding unit_encoding (list_encoding (footprint_encoding ET))) (inr fs)
  end.

Definition memo_key {N E} (EN : encoding N) (EE : encoding E) :=
  pair_encoding positive_encoding (memory_version_encoding EN EE).

Inductive audit_memory_version_event (N E CN CE : Type) : Type :=
  | AuditVersionLive
  | AuditVersionPhi (node : N) (code : positive) (events : list CN)
  | AuditVersionDef (edge : E) (index : nat) (code : positive)
      (events : list (audit_pair_event E nat CE audit_nat_encoding_event)).

Arguments AuditVersionLive {N E CN CE}.
Arguments AuditVersionPhi {N E CN CE} _ _ _.
Arguments AuditVersionDef {N E CN CE} _ _ _ _.

(** Definition versions compose the actual edge and unary-index encoder executions. *)
Definition audit_memory_version_encode {N E CN CE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (input : memory_version N E) : positive * list (audit_memory_version_event N E CN CE) :=
  match input with
  | MemoryLive => (xH, [AuditVersionLive])
  | MemoryPhi n =>
      let '(code, events) := node_enc n in (xO code, [AuditVersionPhi n code events])
  | MemoryDef e i =>
      let '(code, events) := audit_pair_encode edge_enc audit_nat_encode (e, i) in
      (xI code, [AuditVersionDef e i code events])
  end.

(** Matching node and edge encoders yield the existing tagged memory-version code. *)
Definition audit_memory_version_encode_erases_statement : Prop :=
  forall N E CN CE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE) input,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    fst (audit_memory_version_encode node_enc edge_enc input) =
      encode (memory_version_encoding EN EE) input.

(** Each footprint uses the exact nested site and signed-endpoint pair encoders. *)
Definition audit_memory_footprint_encode {T CE} (site_enc : T -> positive * list CE)
    (input : footprint T) :=
  audit_pair_encode site_enc (audit_pair_encode audit_z_encode audit_z_encode)
    (fp_site input, (fp_lo input, fp_hi input)).

(** A matching site encoder yields the existing footprint code, including both endpoints. *)
Definition audit_memory_footprint_encode_erases_statement : Prop :=
  forall T CE (ET : encoding T) (site_enc : T -> positive * list CE) input,
    (forall t, fst (site_enc t) = encode ET t) ->
    fst (audit_memory_footprint_encode site_enc input) = encode (footprint_encoding ET) input.

(** Scope coding preserves the selected sum branch and every footprint-list child trace. *)
Definition audit_memory_scope_encode {T CE} (site_enc : T -> positive * list CE)
    (input : memory_scope T) :=
  audit_sum_encode audit_unit_encode (audit_list_encode (audit_memory_footprint_encode site_enc))
    (
      match input with
      | MemoryAll => inl tt
      | MemoryRegions fs => inr fs
      end).

(** A matching site encoder yields the scope code for both all-memory and region cases. *)
Definition audit_memory_scope_encode_erases_statement : Prop :=
  forall T CE (ET : encoding T) (site_enc : T -> positive * list CE) input,
    (forall t, fst (site_enc t) = encode ET t) ->
    fst (audit_memory_scope_encode site_enc input) = scope_code ET input.

(** Memo keys combine the scope code with the same observed version encoding. *)
Definition audit_memory_memo_key_encode {N E CN CE}
    (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE)
    (input : positive * memory_version N E) :=
  audit_pair_encode audit_positive_encode (audit_memory_version_encode node_enc edge_enc) input.

(** Matching component encoders yield the existing scope-and-version memo key code. *)
Definition audit_memory_memo_key_encode_erases_statement : Prop :=
  forall N E CN CE (EN : encoding N) (EE : encoding E)
      (node_enc : N -> positive * list CN) (edge_enc : E -> positive * list CE) input,
    (forall n, fst (node_enc n) = encode EN n) ->
    (forall e, fst (edge_enc e) = encode EE e) ->
    fst (audit_memory_memo_key_encode node_enc edge_enc input) = encode (memo_key EN EE) input.

(** * Deterministic nested event folds *)

Fixpoint audit_memory_version_work {N E CN CE} (node_work : list CN -> nat)
    (edge_work : list CE -> nat) (events : list (audit_memory_version_event N E CN CE)) : nat :=
  match events with
  | [] => 0
  | AuditVersionLive :: rest => 1 + audit_memory_version_work node_work edge_work rest
  | AuditVersionPhi _ _ child :: rest => 1 + node_work child +
      audit_memory_version_work node_work edge_work rest
  | AuditVersionDef _ _ _ child :: rest =>
      1 + audit_pair_events_work edge_work audit_nat_events_work child +
        audit_memory_version_work node_work edge_work rest
  end.

(** A footprint event pairs site-encoding events with the two signed endpoint encodings. *)
Definition audit_memory_footprint_event (T CE : Type) : Type :=
  audit_pair_event T (Z * Z) CE
    (audit_pair_event Z Z (audit_basic_encoding_event Z) (audit_basic_encoding_event Z)).

Definition audit_memory_footprint_work {T CE} (site_work : list CE -> nat)
    (events : list (audit_memory_footprint_event T CE)) : nat :=
  audit_pair_events_work site_work
    (audit_pair_events_work audit_basic_encoding_work audit_basic_encoding_work) events.

(** A scope event records the all-memory unit branch or the list of footprint encodings. *)
Definition audit_memory_scope_event (T CE : Type) : Type :=
  audit_sum_event unit (list (footprint T)) (audit_basic_encoding_event unit)
    (audit_list_event (footprint T) (audit_memory_footprint_event T CE)).

Definition audit_memory_scope_work {T CE} (site_work : list CE -> nat)
    (events : list (audit_memory_scope_event T CE)) : nat :=
  audit_sum_events_work audit_basic_encoding_work
    (audit_list_events_work (audit_memory_footprint_work site_work)) events.

Definition audit_memory_memo_key_work {N E CN CE} (node_work : list CN -> nat)
    (edge_work : list CE -> nat)
    (events : list (audit_pair_event positive (memory_version N E)
      (audit_basic_encoding_event positive) (audit_memory_version_event N E CN CE))) : nat :=
  audit_pair_events_work audit_basic_encoding_work (audit_memory_version_work node_work edge_work)
    events.

(** The budget sums the actual footprint children and emitted positive-code sizes. *)
Fixpoint audit_memory_footprint_list_work {T CE} (site_enc : T -> positive * list CE)
    (site_work : list CE -> nat) (input : list (footprint T)) : nat :=
  match input with
  | [] => 0
  | fp :: rest =>
      audit_memory_footprint_work site_work (snd (audit_memory_footprint_encode site_enc fp)) +
        audit_memory_footprint_list_work site_enc site_work rest
  end.

Definition audit_memory_scope_budget {T CE} (site_enc : T -> positive * list CE)
    (site_work : list CE -> nat) (input : memory_scope T) : nat :=
  match input with
  | MemoryAll => 2
  | MemoryRegions fs =>
      5 + 2 * length fs + 10 * audit_encoded_bits (audit_memory_footprint_encode site_enc) fs +
        audit_memory_footprint_list_work site_enc site_work fs
  end.

(** Scope encoding charges are bounded using the actual encoded sites and their captured work. *)
Definition audit_memory_scope_work_bound_statement : Prop :=
  forall T CE (site_enc : T -> positive * list CE) site_work q,
    audit_memory_scope_work site_work (snd (audit_memory_scope_encode site_enc q)) <=
      audit_memory_scope_budget site_enc site_work q.
