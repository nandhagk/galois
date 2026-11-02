(** * Legacy slice encoder agreement

    These examples exercise the full counted slice with faithful and colliding encoders.
    For example, disconnected Boolean nodes expose disagreement at [true].
    Builds on: legacy full-slice and graph DFS models. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet.
From Galois.Domains Require Import DomainsFootprint.
From Galois.Graph Require Import GraphCore GraphPrepare GraphDfs GraphAuditDfs.
From Galois.Analyses Require Import AnalysesAuditMemoryLegacySlice
  AnalysesAuditMemoryLegacySliceFull.
Import List.ListNotations.

Definition encoder_graph : Graph.t bool bool :=
  Graph.Make [false] [false; true] (fun _ => []) (fun e => e) (fun e => e).

Definition encoder_prep := prepare bool_encoding encoder_graph.

Definition faithful_code (n : bool) := (encode bool_encoding n, [tt]).

Definition colliding_code (_ : bool) := (encode bool_encoding false, @nil unit).

Definition encoder_site_code (_ : unit) := (encode unit_encoding tt, @nil unit).

Definition encoder_writes (_ : bool) := (@nil (footprint unit), [tt]).

Definition encoder_work (xs : list unit) := length xs.

Definition faithful_events := snd (audit_legacy_slice_full bool_encoding unit_encoding
  faithful_code encoder_site_code encoder_graph encoder_prep encoder_writes [] [false] false).

Example faithful_node_encoder_agrees :
  forall n, fst (faithful_code n) = encode bool_encoding n.
Proof.
  intros []; reflexivity.
Qed.

Example colliding_node_encoder_disagrees :
  fst (colliding_code true) <> encode bool_encoding true.
Proof.
  vm_compute; discriminate.
Qed.

Example colliding_node_encoder_not_agrees :
  ~ (forall n, fst (colliding_code n) = encode bool_encoding n).
Proof.
  intro Hagrees.
  exact (colliding_node_encoder_disagrees (Hagrees true)).
Qed.

Example faithful_dfs_traces_nonempty :
  (Nat.ltb 0 (length (audit_legacy_slice_forward_dfs faithful_events)),
   Nat.ltb 0 (length (audit_legacy_slice_reverse_dfs faithful_events))) = (true, true).
Proof.
  vm_compute; reflexivity.
Qed.

Example faithful_slice_trace_nonempty :
  length (audit_legacy_slice_node_checks faithful_events) = 3.
Proof.
  vm_compute; reflexivity.
Qed.

Example faithful_slice_trace_within_budget :
  Nat.leb (audit_legacy_slice_source_work encoder_work encoder_work encoder_work
    (audit_legacy_slice_node_checks faithful_events))
    (audit_legacy_slice_budget faithful_code encoder_site_code encoder_writes encoder_work
      encoder_work encoder_work [] (visited (dfs encoder_prep FinSet.empty [false]))
      (visited (dfs (prepared_reverse encoder_prep [false]) FinSet.empty [false]))
      (Graph.nodes encoder_graph)) = true.
Proof.
  vm_compute; reflexivity.
Qed.
