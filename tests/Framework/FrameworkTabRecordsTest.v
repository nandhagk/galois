(** * Actual tabulator bucket ownership clients

    Distinct caller roots and exploded return facts coexist in their actual runtime buckets.
    For example, two callers of the same entry fact retain both canonical incoming records.
    Builds on: FrameworkTabRecords and the actual taint fixture. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Program Require Import ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkIde FrameworkTabulate FrameworkTabPaths
  FrameworkTabRecords FrameworkTabJumpProgress.
From Galois.Tests.Framework Require Import FrameworkIdeTest.
Import List.ListNotations.

Definition call_arc := Jump.Arc 0 (0, @None unit) (1, None) (Icfg.Call 7) true.
Definition end_none := Jump.Arc 2 (2, @None unit) (3, None) (Icfg.Return 7) true.
Definition end_fact := Jump.Arc 2 (2, Some tt) (3, Some tt) (Icfg.Return 7) true.

Definition empty_state : Tab.state nat nat nat unit bool :=
  Tab.State Map.empty Map.empty Map.empty [] FinSet.empty.

Definition first_caller :=
  Cost.value (Tab.call_c ifds_ide (0, None) call_arc empty_state).

Definition two_callers :=
  Cost.value (Tab.call_c ifds_ide (0, Some tt) call_arc first_caller).

Definition two_ends :=
  Cost.value (Tab.end_c ifds_ide (1, None) end_fact
    (Cost.value (Tab.end_c ifds_ide (1, None) end_none empty_state))).

Example actual_callers_coexist :
  (Map.get positive_encoding
    (encode (Tab.incoming_enc ifds_ide) ((0, None), Tab.arc_key call_arc))
    (TabRecords.callers ifds_ide two_callers (1, None)),
   Map.get positive_encoding
    (encode (Tab.incoming_enc ifds_ide) ((0, Some tt), Tab.arc_key call_arc))
    (TabRecords.callers ifds_ide two_callers (1, None))) =
    (Some ((0, None), call_arc), Some ((0, Some tt), call_arc)).
Proof.
  vm_compute; reflexivity.
Qed.

Example actual_ends_coexist :
  (Map.get positive_encoding (encode (Tab.arc_enc ifds_ide) (Tab.arc_key end_none))
    (TabRecords.ends ifds_ide two_ends (1, None)),
   Map.get positive_encoding (encode (Tab.arc_enc ifds_ide) (Tab.arc_key end_fact))
    (TabRecords.ends ifds_ide two_ends (1, None))) = (Some end_none, Some end_fact).
Proof.
  vm_compute; reflexivity.
Qed.

Example wrong_callee_bucket_is_empty :
  Map.elements (TabRecords.callers ifds_ide two_callers (2, None)) = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_end_bucket_is_empty :
  Map.elements (TabRecords.ends ifds_ide empty_state (1, None)) = [].
Proof.
  vm_compute; reflexivity.
Qed.

(** Every actual raw run retains owned buckets independently of success or Micro semantics. *)
Example actual_raw_bucket_ownership fuel :
  match Tab.raw ifds_ide 0 fuel with
  | inl s | inr s => TabRecords.invariant ifds_ide 0 s
  end.
Proof.
  apply TabRecords.raw_invariant.
  apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
  apply FrameworkKey.option_laws; exact unit_encoding_laws.
Qed.

Local Lemma call_arc_member : In call_arc (Jump.arcs ifds_ide).
Proof.
  rewrite Jump.arcs_equation; vm_compute; auto.
Qed.

Local Lemma first_caller_valid : TabRecords.valid ifds_ide 0 first_caller.
Proof.
  apply TabRecords.call_valid.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - apply TabRecords.empty_valid.
  - rewrite TabPaths.roots_value; vm_compute; auto.
  - exact call_arc_member.
  - exists 7; reflexivity.
Qed.

(** An importing preservation client discharges actual vertex and occurrence encoding duties. *)
Example canonical_caller_is_not_overwritten :
  TabRecords.caller_at ifds_ide two_callers (0, None) call_arc.
Proof.
  apply (TabRecords.call_keeps_caller ifds_ide 0 (0, Some tt) call_arc first_caller
    (0, None) call_arc).
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - apply Tab.incoming_enc_laws.
    + apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
      apply FrameworkKey.option_laws; exact unit_encoding_laws.
    + apply Tab.arc_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - exact first_caller_valid.
  - exact call_arc_member.
  - apply TabRecords.call_installs with (start := 0); apply TabRecords.empty_valid.
Qed.

(** Actual affine arc keys determine their weights without enumerating the function carrier. *)
Example affine_arc_key_determines_observations a b :
  In a (Jump.arcs affine) -> In b (Jump.arcs affine) ->
  Tab.arc_key a = Tab.arc_key b -> a = b.
Proof.
  apply TabRecords.arc_key_injective.
Qed.

(** Actual jump runs keep coherent pending membership and finite encoded storage support. *)
Example actual_raw_keys_and_owned_buckets fuel :
  match Tab.raw ifds_ide 0 fuel with
  | inl s | inr s => TabJumpProgress.invariant ifds_ide 0 s
  end.
Proof.
  apply TabJumpProgress.raw_invariant.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - apply jkey_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
Qed.
