(** * Original balanced and pending-call exactness clients

    The actual IFDS engines compute true precisely for original path witnesses.
    For example, the finite-height client certifies both phases without supplied results.
    Builds on: FrameworkTabReach and the existing matched and wrong-site fixtures. *)

From Stdlib Require Import List PArith.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeSimple.
From Galois.Framework Require Import FrameworkUtil FrameworkIfds FrameworkIde FrameworkStack
  FrameworkTabulate FrameworkTabValues FrameworkTabPaths FrameworkTabReach
  FrameworkTabJumpProgress FrameworkTabValueProgress.
From Galois.Tests.Framework Require Import FrameworkIdeTest FrameworkTabulateTest
  FrameworkTabSoundTest.
Import List.ListNotations.

(** The original unit-valued IFDS adapter has reverse and forward balanced exactness. *)
Example original_boolean_balanced_exact fuel c n d :
  Tab.tabulate ifds_ide 0 fuel = Tab.Certified c ->
  (Jump.lookup ifds_ide (proj1_sig c) ((0, None), (n, d)) = true <->
    Stack.balanced taint 0 None n d).
Proof.
  intro Hrun; apply (TabReach.ifds_balanced_exact taint 0 fuel c (0, None) n d).
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - apply jkey_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - exact nat_encoding_laws.
  - exact taint_flow_closed.
  - exact Logic.I.
  - rewrite TabPaths.roots_value; vm_compute; auto.
  - exact Hrun.
Qed.

(** This total client proves original prefix exactness without a successful-run premise. *)
Example actual_total_prefix_exactness :
  exists jumps values,
    TabJumpProgress.complete (TabValues.reach_ide taint) 0 bool_height = Tab.Certified jumps /\
    TabValueProgress.complete (TabValues.reach_ide taint) (proj1_sig jumps)
      (0, None) true bool_height = TabValues.Certified values /\
    forall n d,
      TabValues.lookup (TabValues.reach_ide taint) (proj1_sig values) (n, d) = true <->
        exists stack, Stack.path taint (0, None, []) (n, d, stack).
Proof.
  destruct (TabReach.complete_exact taint (0, None)
    nat_encoding_laws nat_encoding_laws unit_encoding_laws nat_encoding_laws
    taint_graph_wf taint_flow_closed Logic.I) as
    [jumps [values [Hjump [Hvalue [Hbalanced Hprefix]]]]].
  exists jumps, values; split; [exact Hjump|]; split; [exact Hvalue|exact Hprefix].
Qed.

Definition reached (ip : Ifds.t nat nat nat unit) n d :=
  match TabJumpProgress.complete (TabValues.reach_ide ip) 0 bool_height with
  | Tab.Certified jumps =>
    match TabValueProgress.complete (TabValues.reach_ide ip) (proj1_sig jumps)
      (0, None) true bool_height with
    | TabValues.Certified values =>
      Some (TabValues.lookup (TabValues.reach_ide ip) (proj1_sig values) (n, d))
    | _ => None
    end
  | _ => None
  end.

Example pending_call_is_reached :
  reached taint 2 (Some tt) = Some true.
Proof.
  vm_compute; reflexivity.
Qed.

Example wrong_site_cannot_reach_the_return_target :
  reached wrong_returns 3 None = Some false.
Proof.
  vm_compute; reflexivity.
Qed.

Example unlisted_empty_start_is_reached :
  reached empty_ifds 0 None = Some true.
Proof.
  vm_compute; reflexivity.
Qed.
