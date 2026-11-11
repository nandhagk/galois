(** * Composite-key budget clients

    Clients derive tabulation key charges from the genuine scalar encoding callbacks.
    For example, an absent fact still contributes its serialized optional tag.
    Builds on: FrameworkTabEncodingCost and the taint presentation. *)

From Stdlib Require Import NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabEncodingCost.
From Galois.Tests.Framework Require Import FrameworkIdeTest.

Example optional_zero_width :
  key_bits (FrameworkKey.option unit_encoding) None = 7%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example scalar_width_does_not_price_a_composite_key :
  (key_bits (IdeValue.key_enc ifds_ide) (0, None),
   key_bits (Jump.enc ifds_ide) ((0, None), (0, None))) = (23, 99)%N.
Proof.
  vm_compute; reflexivity.
Qed.

Example incoming_key_retains_all_components :
  let a := Jump.Arc 0 (0, None) (1, None) (Icfg.Call 7) true in
  key_bits (Tab.incoming_enc ifds_ide) ((0, None), Tab.arc_key a) = 211%N.
Proof.
  vm_compute; reflexivity.
Qed.

(** An arbitrary client composes local primitive budgets without a whole-operation price. *)
Example scalar_budgets_give_jump_budgets {N E P D A F} (I : Ide.t N E P D A F)
    r x n y en ed wn wd :
  TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) r en wn ->
  TabEncodingCost.bounded (Cfg.node_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) n en wn ->
  (match x with
   | Some d => TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d ed wd
   | None => True
   end) ->
  (match y with
   | Some d => TabEncodingCost.bounded (Ifds.fact_enc (Ide.ifds I)) d ed wd
   | None => True
   end) ->
  let vw := TabEncodingCost.pair_width wn (TabEncodingCost.option_width wd) in
  let ve := TabEncodingCost.pair_charge en (TabEncodingCost.option_charge ed wd)
    wn (TabEncodingCost.option_width wd) in
  TabEncodingCost.bounded (Jump.enc I) ((r, x), (n, y))
    (TabEncodingCost.pair_charge ve ve vw vw) (TabEncodingCost.pair_width vw vw).
Proof.
  intros Hr Hn Hx Hy; apply TabEncodingCost.jump_bounded;
    apply TabEncodingCost.vertex_bounded; assumption.
Qed.
