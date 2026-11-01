(** * Memory scope and initial memo adequacy

    These proofs establish scope-code injectivity and the initial and busy-cut properties.
    For example, a busy cut includes its starting version in every walk trace.
    Builds on: memory state contracts, canonical encodings and map lookup laws. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryWalk AnalysesAuditMemoryEncoding
  AnalysesAuditMemoryState.
Import List.ListNotations.

(** * Scope codes and memo initialization *)

(** Equal scope codes imply equal scopes, including the all-memory branch. *)
Theorem scope_code_injective : scope_code_injective_statement.
Proof.
  unfold scope_code_injective_statement, scope_code.
  intros T ET [a|] [b|] Heq; try discriminate; try reflexivity.
  apply (encode_injective (sum_encoding unit_encoding (list_encoding (footprint_encoding ET))))
    in Heq; inversion Heq; reflexivity.
Qed.

(** An empty memo contains no busy or completed entries and has prepared indexes. *)
Theorem memo_initial : memo_initial_statement.
Proof.
  unfold memo_initial_statement, memo_valid, AnalysesAuditMemoryState.memo_initial.
  intros N E T EN EE ET g effects mg; simpl.
  split; [reflexivity|]. split; [reflexivity|]. split; [apply Map.wf_empty|]. split.
  - intros k; rewrite Map.get_empty; discriminate.
  - intros q start roots Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

(** * Busy cuts *)

(** A busy cut is incomplete and includes any occurrence of its starting version. *)
Theorem busy_cut_coverage : busy_cut_coverage_statement.
Proof.
  unfold busy_cut_coverage_statement, busy_cut.
  intros N E v trace Hin; simpl. split; [reflexivity|].
  exists v; split; [exact Hin|simpl; auto].
Qed.

(** Every walk starts with its version, so its busy cut intersects the walk. *)
Theorem busy_cut_trace : busy_cut_trace_statement.
Proof.
  unfold busy_cut_trace_statement.
  intros N E T ET effects mg q v trace Htrace.
  apply busy_cut_coverage. inversion Htrace; subst; simpl; auto.
Qed.
