(** * Actual jump record support and enumeration cost clients

    Every raw state has bounded replay buckets even when execution exhausts its budget.
    For example, the same supplied root and arc bound covers every callee bucket.
    Builds on: FrameworkTabRecordCost and FrameworkTabJumpProgress. *)

From Stdlib Require Import List NArith PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseTrieCost.
From Galois.Framework Require Import FrameworkUtil FrameworkIde FrameworkTabulate FrameworkTabPaths
  FrameworkTabRecords FrameworkTabJumpProgress FrameworkTabRecordCost.
From Galois.Tests.Framework Require Import FrameworkIdeTest.
Import List.ListNotations.

(** Actual exhausted and stopped states share the proved finite incoming-record support. *)
Example raw_caller_cardinality fuel entry :
  match Tab.raw ifds_ide 0 fuel with
  | inl s | inr s =>
    (Map.size (TabRecords.callers ifds_ide s entry) <=
      length (TabPaths.roots ifds_ide 0) * length (Jump.arcs ifds_ide))%nat
  end.
Proof.
  pose proof (TabRecords.raw_invariant ifds_ide 0) as Hvalid.
  assert (HV : encoding_laws (IdeValue.key_enc ifds_ide)).
  { apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws. }
  specialize (Hvalid HV fuel).
  destruct (Tab.raw ifds_ide 0 fuel); apply TabRecordCost.caller_size; exact (proj1 Hvalid).
Qed.

(** This bound retains physical enumeration work and the full supplied root-by-arc inventory. *)
Example actual_caller_enumeration fuel entry w :
  (forall root a, In root (TabPaths.roots ifds_ide 0) -> In a (Jump.arcs ifds_ide) ->
    (key_bits (Tab.incoming_enc ifds_ide) (root, Tab.arc_key a) <= w)%N) ->
  match Tab.raw ifds_ide 0 fuel with
  | inl s | inr s =>
    (Cost.ticks (Map.elements_c (TabRecords.callers ifds_ide s entry)) <=
      TrieCost.trie_k * (1 +
        N.of_nat (length (TabPaths.roots ifds_ide 0%nat)) *
        N.of_nat (length (Jump.arcs ifds_ide)) * w))%N
  end.
Proof.
  intro Hwidth; pose proof (TabRecords.raw_invariant ifds_ide 0) as Hvalid.
  assert (HV : encoding_laws (IdeValue.key_enc ifds_ide)).
  { apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws. }
  specialize (Hvalid HV fuel); destruct (Tab.raw ifds_ide 0 fuel) as [s|s].
  - apply TabRecordCost.caller_enumeration_cost; [exact (proj1 Hvalid)|exact Hwidth].
  - apply TabRecordCost.caller_enumeration_cost; [exact (proj1 Hvalid)|exact Hwidth].
Qed.
