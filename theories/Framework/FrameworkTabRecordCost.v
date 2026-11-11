(** * Finite record support and charged replay enumeration

    Actual caller and end buckets have finite support in the supplied root and arc inventories.
    For example, repeated registration cannot grow a bucket beyond its canonical incoming codes.
    Builds on: FrameworkTabRecords, BaseMapCost and BaseMap finite-support bounds. *)

From Stdlib Require Import List Arith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseMapCost BaseTrieCost.
From Galois.Framework Require Import FrameworkIfds FrameworkIde FrameworkTabulate FrameworkTabPaths
  FrameworkTabRecords.
Import List.ListNotations.

Module TabRecordCost.

Local Lemma nat_N_le a b : (a <= b)%nat -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  intro Hle; apply (proj1 (N.compare_le_iff _ _)).
  rewrite <- Nat2N.inj_compare; apply (proj2 (Nat.compare_le_iff _ _)); exact Hle.
Qed.

(** The support retains every supplied root and arc occurrence, including unreachable ones. *)
Definition caller_codes {N E P D A F} (I : Ide.t N E P D A F) start :=
  flat_map (fun root =>
    map (fun a => encode (Tab.incoming_enc I) (root, Tab.arc_key a)) (Jump.arcs I))
    (TabPaths.roots I start).

Definition end_codes {N E P D A F} (I : Ide.t N E P D A F) :=
  map (fun a => encode (Tab.arc_enc I) (Tab.arc_key a)) (Jump.arcs I).

Local Lemma caller_codes_length {N E P D A F} (I : Ide.t N E P D A F) start :
  length (caller_codes I start) =
    (length (TabPaths.roots I start) * length (Jump.arcs I))%nat.
Proof.
  unfold caller_codes; induction (TabPaths.roots I start) as [|root roots IH];
    cbn [flat_map length].
  - reflexivity.
  - rewrite length_app, length_map, IH; lia.
Qed.

(** Every stored caller code belongs to the full root-by-arc support. *)
Theorem caller_support {N E P D A F} (I : Ide.t N E P D A F) start s entry code payload :
  TabRecords.valid I start s ->
  Map.get positive_encoding code (TabRecords.callers I s entry) = Some payload ->
  In code (caller_codes I start).
Proof.
  intros Hvalid Hget; destruct payload as [root a].
  destruct (TabRecords.caller_payload Hvalid entry code root a Hget) as
    [Hroot [Ha [Hkind [Hentry Hcode]]]].
  rewrite Hcode; unfold caller_codes; apply in_flat_map; exists root.
  split; [exact Hroot|apply in_map_iff; exists a; split; [reflexivity|exact Ha]].
Qed.

(** Every stored end code belongs to the actual prepared arc support. *)
Theorem end_support {N E P D A F} (I : Ide.t N E P D A F) start s entry code a :
  TabRecords.valid I start s ->
  Map.get positive_encoding code (TabRecords.ends I s entry) = Some a ->
  In code (end_codes I).
Proof.
  intros Hvalid Hget.
  destruct (TabRecords.end_payload Hvalid entry code a Hget) as
    [Hentry [Ha [Hkind Hcode]]].
  rewrite Hcode; apply in_map_iff; exists a; split; [reflexivity|exact Ha].
Qed.

(** Supplied root and arc occurrences bound canonical caller cardinality without a run premise. *)
Theorem caller_size {N E P D A F} (I : Ide.t N E P D A F) start s entry :
  TabRecords.valid I start s ->
  (Map.size (TabRecords.callers I s entry) <=
    length (TabPaths.roots I start) * length (Jump.arcs I))%nat.
Proof.
  intro Hvalid; rewrite <- caller_codes_length.
  apply (Map.size_support_bound positive_encoding positive_encoding_laws).
  - exact (TabRecords.caller_buckets_wf Hvalid entry).
  - intros code payload Hget; apply (caller_support I start s entry code payload); assumption.
Qed.

(** Canonical end cardinality is bounded by supplied exploded arc occurrences. *)
Theorem end_size {N E P D A F} (I : Ide.t N E P D A F) start s entry :
  TabRecords.valid I start s ->
  (Map.size (TabRecords.ends I s entry) <= length (Jump.arcs I))%nat.
Proof.
  intro Hvalid; replace (length (Jump.arcs I)) with (length (end_codes I))
    by (unfold end_codes; rewrite length_map; reflexivity).
  apply (Map.size_support_bound positive_encoding positive_encoding_laws).
  - exact (TabRecords.end_buckets_wf Hvalid entry).
  - intros code a Hget; apply (end_support I start s entry code a); assumption.
Qed.

(** The actual caller replay list retains the full finite occurrence bound. *)
Theorem caller_length {N E P D A F} (I : Ide.t N E P D A F) start s entry :
  TabRecords.valid I start s ->
  (length (Map.elements (TabRecords.callers I s entry)) <=
    length (TabPaths.roots I start) * length (Jump.arcs I))%nat.
Proof.
  rewrite <- Map.size_elements; apply caller_size.
Qed.

(** The actual end replay list retains the full finite occurrence bound. *)
Theorem end_length {N E P D A F} (I : Ide.t N E P D A F) start s entry :
  TabRecords.valid I start s ->
  (length (Map.elements (TabRecords.ends I s entry)) <= length (Jump.arcs I))%nat.
Proof.
  rewrite <- Map.size_elements; apply end_size with (start := start).
Qed.

(** Caller enumeration charges physical trie paths using actual incoming-code widths. *)
Theorem caller_enumeration_cost {N E P D A F} (I : Ide.t N E P D A F) start s entry w :
  TabRecords.valid I start s ->
  (forall root a, In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
    (key_bits (Tab.incoming_enc I) (root, Tab.arc_key a) <= w)%N) ->
  (Cost.ticks (Map.elements_c (TabRecords.callers I s entry)) <=
    TrieCost.trie_k * (1 +
      N.of_nat (length (TabPaths.roots I start)) * N.of_nat (length (Jump.arcs I)) * w))%N.
Proof.
  intros Hvalid Hwidth.
  pose proof (MapCost.elements_numeric_cost positive_encoding
    (TabRecords.callers I s entry) w (TabRecords.caller_buckets_wf Hvalid entry)) as Hcost.
  assert (Hbits : forall code payload,
    Map.get positive_encoding code (TabRecords.callers I s entry) = Some payload ->
    (key_bits positive_encoding code <= w)%N).
  { intros code [root a] Hget.
    destruct (TabRecords.caller_payload Hvalid entry code root a Hget) as
      [Hroot [Ha [Hkind [Hentry Hcode]]]].
    subst code; rewrite positive_encoding_bits; exact (Hwidth root a Hroot Ha). }
  specialize (Hcost Hbits).
  pose proof (caller_size I start s entry Hvalid) as Hsize.
  apply nat_N_le in Hsize; rewrite Nat2N.inj_mul in Hsize.
  eapply N.le_trans; [exact Hcost|].
  apply N.mul_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r; exact Hsize.
Qed.

(** End enumeration charges physical trie paths using the actual encoded arc occurrence widths. *)
Theorem end_enumeration_cost {N E P D A F} (I : Ide.t N E P D A F) start s entry w :
  TabRecords.valid I start s ->
  (forall a, In a (Jump.arcs I) -> (key_bits (Tab.arc_enc I) (Tab.arc_key a) <= w)%N) ->
  (Cost.ticks (Map.elements_c (TabRecords.ends I s entry)) <=
    TrieCost.trie_k * (1 + N.of_nat (length (Jump.arcs I)) * w))%N.
Proof.
  intros Hvalid Hwidth.
  pose proof (MapCost.elements_numeric_cost positive_encoding
    (TabRecords.ends I s entry) w (TabRecords.end_buckets_wf Hvalid entry)) as Hcost.
  assert (Hbits : forall code a,
    Map.get positive_encoding code (TabRecords.ends I s entry) = Some a ->
    (key_bits positive_encoding code <= w)%N).
  { intros code a Hget.
    destruct (TabRecords.end_payload Hvalid entry code a Hget) as
      [Hentry [Ha [Hkind Hcode]]].
    subst code; rewrite positive_encoding_bits; exact (Hwidth a Ha). }
  specialize (Hcost Hbits).
  pose proof (end_size I start s entry Hvalid) as Hsize.
  apply nat_N_le in Hsize.
  eapply N.le_trans; [exact Hcost|].
  apply N.mul_le_mono_l, N.add_le_mono_l, N.mul_le_mono_r; exact Hsize.
Qed.

End TabRecordCost.
