(** * Adequacy of legacy successor enumeration

    The counted lookup and target traversal preserve the original successor order.
    For example, two parallel edges retain two target occurrences.
    Builds on: AnalysesAuditMemoryLegacySuccessor and counted map adequacy. *)

From Stdlib Require Import List.
From Galois.Graph Require Import GraphCore GraphPrepare.
From Galois.Collections Require Import CollectionsAuditMap CollectionsAuditMapAdequacy.
From Galois.Analyses Require Import AnalysesMemoryLegacy AnalysesAuditMemoryLegacySuccessor.

(** * Target traversal *)

(** Mapping targets in the observer preserves the source list and its order. *)
Lemma audit_legacy_successor_map_erases N E CN (g : Graph.t N E) edges :
    fst (@audit_legacy_successor_map N E CN g edges) = map (Graph.target g) edges.
Proof.
  induction edges as [|edge rest IH].
  - reflexivity.
  - cbn [audit_legacy_successor_map map].
    destruct (audit_legacy_successor_map g rest) as [targets events]; cbn in *.
    rewrite IH; reflexivity.
Qed.

(** Matching node encodings preserve the original indexed successor enumeration. *)
Theorem audit_legacy_successors_erases : audit_legacy_successors_erases_statement.
Proof.
  intros N E CN EN node_enc g p node Henc.
  pose proof (audit_map_get_erases N (list E) CN node_enc EN node (out_index p) (Henc node))
    as Hlookup.
  unfold audit_legacy_successors_counted, legacy_successors, succ_edges, index_edges.
  destruct (audit_map_get node_enc node (out_index p)) as [found calls] eqn:Hget.
  cbn in Hlookup; rewrite <- Hlookup.
  destruct found as [edges|].
  -
    pose proof (audit_legacy_successor_map_erases N E CN g edges) as Hmap.
    destruct (audit_legacy_successor_map g edges); cbn in *; exact Hmap.
  - reflexivity.
Qed.
