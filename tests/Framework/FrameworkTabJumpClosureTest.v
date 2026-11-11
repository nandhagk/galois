(** * Actual jump closure and finite-height certification clients

    Completion discharges its own checker duties on arbitrary lawful dictionaries.
    For example, the non-strict composition control also certifies every ground row.
    Builds on: FrameworkTabJumpClosure and the actual IFDS and non-strict fixtures. *)

From Stdlib Require Import List PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore LatticeSimple LatticeHeight.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde
  FrameworkTabulate FrameworkTabJumpProgress FrameworkTabJumpClosure.
From Galois.Tests.Framework Require Import FrameworkIdeTest FrameworkTabulateTest
  FrameworkTabSoundTest.
Import List.ListNotations.

(** This client constructs a certificate for any start without a successful-run premise. *)
Example arbitrary_jump_completion {N E P D A F} (I : Ide.t N E P D A F) start
    (H : height (Micro.lat (Ide.micro I))) :
  encoding_laws (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) ->
  lattice_laws (Micro.lat (Ide.micro I)) ->
  exists c, TabJumpProgress.complete I start H = Tab.Certified c.
Proof.
  intros HN HE HD HL; apply TabJumpClosure.complete_certified.
  - apply FrameworkKey.pair_laws; [exact HN|apply FrameworkKey.option_laws; exact HD].
  - apply jkey_enc_laws; assumption.
  - apply Tab.arc_enc_laws; assumption.
  - apply Tab.incoming_enc_laws.
    + apply FrameworkKey.pair_laws; [exact HN|apply FrameworkKey.option_laws; exact HD].
    + apply Tab.arc_enc_laws; assumption.
  - exact HL.
Qed.

(** Every raw stopped candidate is accepted before any certificate is assumed. *)
Example actual_stopped_taint_checked fuel stopped :
  Tab.raw ifds_ide 0 fuel = inr stopped ->
  check_jumps ifds_ide 0 (Tab.jumps stopped) = true.
Proof.
  apply TabJumpClosure.stopped_checked.
  - apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
    apply FrameworkKey.option_laws; exact unit_encoding_laws.
  - apply jkey_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - apply Tab.arc_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - apply Tab.incoming_enc_laws.
    + apply FrameworkKey.pair_laws; [exact nat_encoding_laws|].
      apply FrameworkKey.option_laws; exact unit_encoding_laws.
    + apply Tab.arc_enc_laws; [exact nat_encoding_laws|exact unit_encoding_laws].
  - exact bool_laws.
Qed.

Definition nonstrict_ide : Ide.t nat nat nat unit unit bool :=
  Ide.Make taint unit_lattice nonstrict_micro (fun _ _ _ => Cost.ret true).

(** Non-strict composition inhabits the closure domain without a bottom-annihilation duty. *)
Example nonstrict_completion start :
  exists c, TabJumpProgress.complete nonstrict_ide start bool_height = Tab.Certified c.
Proof.
  apply arbitrary_jump_completion;
    [exact nat_encoding_laws|exact nat_encoding_laws|exact unit_encoding_laws|exact bool_laws].
Qed.

(** An arbitrary unlisted public start still receives and certifies its identity ground rows. *)
Example empty_completion start :
  exists c, TabJumpProgress.complete (Ifds.as_ide empty_ifds) start bool_height = Tab.Certified c.
Proof.
  apply arbitrary_jump_completion;
    [exact nat_encoding_laws|exact nat_encoding_laws|exact unit_encoding_laws|exact bool_laws].
Qed.

Example recursive_completion_certifies :
  match TabJumpProgress.complete (Ifds.as_ide recursive_ifds) 0 bool_height with
  | Tab.Certified _ => true
  | _ => false
  end = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example wrong_return_completion_does_not_invent_a_path :
  match TabJumpProgress.complete (Ifds.as_ide wrong_returns) 0 bool_height with
  | Tab.Certified c =>
    Jump.lookup (Ifds.as_ide wrong_returns) (proj1_sig c) ((0, None), (3, None))
  | _ => true
  end = false.
Proof.
  vm_compute; reflexivity.
Qed.
